use std::{iter::successors, ops::Mul};

use ark_ec::CurveGroup;
use ark_ff::{Field, One, UniformRand, Zero};
use spongefish::{
    DomainSeparator, ProofError, ProofResult, ProverState, VerifierState,
    codecs::arkworks_algebra::{
        FieldDomainSeparator, FieldToUnitDeserialize, FieldToUnitSerialize, GroupDomainSeparator,
        GroupToUnitDeserialize, GroupToUnitSerialize, UnitToField,
    },
};
use tracing::instrument;

use crate::{
    circuit::types::Statement,
    ipa::{extended::ExtendedBulletproofDomainSeparator, types as ipa_types},
    msm::Msm,
    range::types::VectorPolynomial,
    vector_ops::{VectorOps, inner_product, mat_mul_l, mat_mul_r},
};

pub mod types;

pub trait CircuitProofDomainSeparator<G: CurveGroup> {
    fn circuit_proof_statement(self, n: usize) -> Self;
    fn add_circuit_proof(self, n: usize) -> Self;
}

impl<G> CircuitProofDomainSeparator<G> for DomainSeparator
where
    G: CurveGroup,
    Self: GroupDomainSeparator<G> + FieldDomainSeparator<G::ScalarField>,
{
    fn circuit_proof_statement(self, n: usize) -> Self {
        self.add_points(n, "circuit proof statement")
    }

    fn add_circuit_proof(mut self, n: usize) -> Self {
        self = self
            .add_points(3, "round-message: A_i, A_o, S")
            .challenge_scalars(2, "challenge [y,z]")
            .add_points(5, "round-message: T1, T3, T4, T5, T6")
            .challenge_scalars(1, "challenge x")
            .add_scalars(3, "round-message: tau_x, mu, t_hat")
            .add_extended_bulletproof(n);
        self
    }
}

pub fn prove<G: CurveGroup, Rng: rand::Rng>(
    prover_state: &mut ProverState,
    crs: &types::CRS<G>,
    circuit: &types::Circuit<G::ScalarField>,
    witness: &types::Witness<G::ScalarField>,
    rng: &mut Rng,
) -> ProofResult<Vec<u8>> {
    let n = circuit.dim();
    assert!(
        crs.size() >= circuit.dim(),
        "CRS size must be gte circuit dimension"
    );
    let gs = &crs.ipa_crs.gs[0..n];
    let hs = &crs.ipa_crs.hs[0..n];
    let q = circuit.size();
    let [alpha, beta, rho]: [G::ScalarField; 3] =
        std::array::from_fn(|_| G::ScalarField::rand(rng));

    // Generate s_l and s_r vectors needed for s computation
    let s_l = (0..n)
        .map(|_| G::ScalarField::rand(rng))
        .collect::<Vec<_>>();
    let s_r = (0..n)
        .map(|_| G::ScalarField::rand(rng))
        .collect::<Vec<_>>();

    // Compute a_i, a_o, and s in parallel
    let (a_i, (a_o, s)) = rayon::join(
        || {
            crs.h.mul(alpha) + {
                let bases: Vec<G::Affine> = gs.iter().chain(hs.iter()).copied().collect();
                let scalars: Vec<G::ScalarField> = witness
                    .a_l
                    .iter()
                    .chain(witness.a_r.iter())
                    .copied()
                    .collect();
                G::msm_unchecked(&bases, &scalars)
            }
        },
        || {
            rayon::join(
                || crs.h.mul(beta) + G::msm_unchecked(gs, &witness.a_o),
                || {
                    crs.h.mul(rho) + {
                        let bases: Vec<G::Affine> = gs.iter().chain(hs.iter()).copied().collect();
                        let scalars: Vec<G::ScalarField> =
                            s_l.iter().chain(s_r.iter()).copied().collect();
                        G::msm_unchecked(&bases, &scalars)
                    }
                },
            )
        },
    );

    prover_state.add_points(&[a_i, a_o, s])?;
    let [y, z]: [G::ScalarField; 2] = prover_state.challenge_scalars()?;

    let (y_vec, y_inv_vec) = {
        let y_inv = y.inverse().expect("nonzero y");
        successors(
            Some((G::ScalarField::one(), G::ScalarField::one())),
            |(succ_y, succ_y_inv)| Some((*succ_y * y, *succ_y_inv * y_inv)),
        )
        .take(n)
        .unzip::<_, _, Vec<_>, Vec<_>>()
    };

    let z_vec: Vec<G::ScalarField> = successors(Some(z), |succ| Some(*succ * z))
        .take(q)
        .collect();

    let l_poly: VectorPolynomial<G::ScalarField> = {
        let v = mat_mul_l(&z_vec, &circuit.w_r);
        let coeffs = vec![
            vec![G::ScalarField::zero(); n],
            witness
                .a_l
                .iter()
                .copied()
                .vector_add(y_inv_vec.iter().copied().hadamard(v))
                .collect(),
            witness.a_o.clone(),
            s_l,
        ];
        VectorPolynomial::new(coeffs, n)
    };
    let r_poly: VectorPolynomial<G::ScalarField> = {
        let v1 = mat_mul_l(&z_vec, &circuit.w_l);
        let v2 = mat_mul_l(&z_vec, &circuit.w_o);
        let coeffs = vec![
            v2.vector_sub(y_vec.iter().copied()).collect(),
            y_vec
                .iter()
                .copied()
                .hadamard(witness.a_r.iter().copied())
                .vector_add(v1)
                .collect(),
            vec![G::ScalarField::zero(); n],
            y_vec
                .iter()
                .copied()
                .hadamard(s_r.iter().copied())
                .collect(),
        ];
        VectorPolynomial::new(coeffs, n)
    };

    let t_poly = l_poly.inner_product(&r_poly);

    // For some reason the paper treats index 2 (or 1 if 0-indexed) differently
    let taus: [Option<G::ScalarField>; 6] = std::array::from_fn(|i| {
        if i == 1 {
            None
        } else {
            Some(G::ScalarField::rand(rng))
        }
    });

    {
        let tts: [G; 5] = taus
            .iter()
            .enumerate()
            .filter_map(|(i, tau_i_opt)| {
                tau_i_opt.map(|tau_i| crs.g.mul(t_poly[i + 1]) + crs.h.mul(tau_i))
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        prover_state.add_points(&tts)?;
    };

    {
        let [x]: [G::ScalarField; 1] = prover_state.challenge_scalars()?;

        let tao_x = {
            let init = x.pow([2])
                * inner_product(
                    z_vec.iter().copied(),
                    mat_mul_r(&circuit.w_v, &witness.gamma),
                );
            taus.iter().enumerate().fold(init, |acc, (i, tau_i_opt)| {
                acc + tau_i_opt
                    .map(|tau_i| tau_i * x.pow([i as u64 + 1]))
                    .unwrap_or(G::ScalarField::zero())
            })
        };

        let mu = alpha * x + beta * x.pow([2]) + rho * x.pow([3]);

        let l = l_poly.evaluate(x);
        let r = r_poly.evaluate(x);

        let witness = ipa_types::Witness::new(l, r);
        let hs_prime = {
            let xs = create_hs_prime::<G>(hs, y);
            G::normalize_batch(
                &xs.iter()
                    .map(|(h, y_inv_i)| h.mul(y_inv_i))
                    .collect::<Vec<_>>(),
            )
        };

        let mut extended_statement: ipa_types::extended::Statement<G> =
            witness.extended_statement(&crs.ipa_crs);

        extended_statement.p += crs.h.mul(-mu);

        prover_state.add_scalars(&[tao_x, mu, extended_statement.c])?;

        let crs = ipa_types::CRS {
            gs: gs.to_vec(),
            hs: hs_prime,
            u: crs.ipa_crs.u,
        };

        crate::ipa::extended::prove(prover_state, &crs, &extended_statement, &witness)?;
    }

    Ok(prover_state.narg_string().to_vec())
}

fn create_hs_prime<G: CurveGroup>(
    hs: &[G::Affine],
    y: G::ScalarField,
) -> Vec<(G::Affine, G::ScalarField)> {
    let y_inv = y.inverse().expect("non-zero y");
    let ys_inv = std::iter::successors(Some(G::ScalarField::one()), |&x| (Some(x * y_inv)));
    hs.iter().copied().zip(ys_inv).collect::<Vec<_>>()
}

pub fn verify_aux<G: CurveGroup, Rng: rand::Rng>(
    verifier_state: &mut VerifierState,
    crs: &types::CRS<G>,
    circuit: &types::Circuit<G::ScalarField>,
    statement: &Statement<G>,
    rng: &mut Rng,
) -> ProofResult<Msm<G>> {
    let n = circuit.dim();
    let q = circuit.size();
    let gs = &crs.ipa_crs.gs[0..n];
    let hs = &crs.ipa_crs.hs[0..n];

    let [a_i, a_o, s]: [G; 3] = verifier_state.next_points()?;
    let [y, z]: [G::ScalarField; 2] = verifier_state.challenge_scalars()?;
    let tts: [Option<G>; 6] = {
        let [tau_1, tau_3, tau_4, tau_5, tau_6]: [G; 5] = verifier_state.next_points()?;
        [
            Some(tau_1),
            None,
            Some(tau_3),
            Some(tau_4),
            Some(tau_5),
            Some(tau_6),
        ]
    };
    let [x]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
    let [tao_x, mu, t_hat]: [G::ScalarField; 3] = verifier_state.next_scalars()?;

    let (y_vec, y_inv_vec) = {
        let y_inv = y.inverse().expect("nonzero y");
        successors(
            Some((G::ScalarField::one(), G::ScalarField::one())),
            |(succ_y, succ_y_inv)| Some((*succ_y * y, *succ_y_inv * y_inv)),
        )
        .take(n)
        .unzip::<_, _, Vec<_>, Vec<_>>()
    };
    let z_vec: Vec<G::ScalarField> = successors(Some(z), |succ| Some(*succ * z))
        .take(q)
        .collect();

    let mut g: Msm<G> = {
        let mut g = Msm::new();

        let delta_y_z = {
            let v = mat_mul_l(&z_vec, &circuit.w_r);
            let l = y_inv_vec.iter().copied().hadamard(v);
            let r = mat_mul_l(&z_vec, &circuit.w_l);
            inner_product(l, r)
        };

        g.upsert_batch(
            G::normalize_batch(&statement.v)
                .into_iter()
                .zip(mat_mul_l(&z_vec, &circuit.w_v).scale(x.square())),
        );

        g.upsert_batch(tts.iter().enumerate().filter_map(|(i, tt_i_opt)| {
            tt_i_opt.map(|tt_i| (tt_i.into_affine(), x.pow([i as u64 + 1])))
        }));

        g.upsert_batch(
            [
                (
                    crs.g.into_affine(),
                    (x.square()
                        * (delta_y_z
                            + inner_product(z_vec.iter().copied(), circuit.c.iter().copied())))
                        - t_hat,
                ),
                (crs.h.into_affine(), -tao_x),
            ]
            .into_iter(),
        );

        g
    };
    let mut msm = {
        let scaled_hs = create_hs_prime::<G>(hs, y);
        let hs_prime = G::normalize_batch(
            &scaled_hs
                .iter()
                .map(|(h, y_inv_i)| h.mul(y_inv_i))
                .collect::<Vec<_>>(),
        );

        let mut p_msm: Msm<G> = Msm::new();

        // Parallel matrix operations
        let (ww_l_result, (ww_r_result, ww_o_result)) = rayon::join(
            || mat_mul_l(&z_vec, &circuit.w_l).scale(x),
            || {
                rayon::join(
                    || mat_mul_l(&z_vec, &circuit.w_r),
                    || mat_mul_l(&z_vec, &circuit.w_o),
                )
            },
        );

        //ww_l
        p_msm.upsert_batch(hs_prime.iter().copied().zip(ww_l_result));

        //ww_r
        p_msm.upsert_batch(
            gs.iter()
                .copied()
                .zip(y_inv_vec.iter().copied().hadamard(ww_r_result).scale(x)),
        );

        //ww_o
        p_msm.upsert_batch(hs_prime.iter().copied().zip(ww_o_result));

        let neg_y_vec = y_vec.iter().map(|yi| -*yi).collect::<Vec<_>>();
        p_msm.upsert_batch(hs_prime.iter().copied().zip(neg_y_vec));

        p_msm.upsert(a_i.into_affine(), x);
        p_msm.upsert(s.into_affine(), x.pow([3]));
        p_msm.upsert(a_o.into_affine(), x.square());
        p_msm.upsert(crs.h.into_affine(), -mu);

        let p: G = p_msm.execute();

        let extended_statement = ipa_types::extended::Statement {
            p,
            c: t_hat,
            witness_size: n,
        };

        let mut msm =
            crate::ipa::extended::verify_aux(verifier_state, &crs.ipa_crs, &extended_statement)?;
        msm.scale_elems(scaled_hs.into_iter());
        Ok::<_, ProofError>(msm)
    }?;

    let alpha = G::ScalarField::rand(rng);
    g.scale(alpha);
    msm.batch(g);

    Ok(msm)
}

#[instrument(skip_all, fields(nbits = statement.v.len()), level = "debug")]
pub fn verify<G: CurveGroup, Rng: rand::Rng>(
    verifier_state: &mut spongefish::VerifierState,
    crs: &types::CRS<G>,
    circuit: &types::Circuit<G::ScalarField>,
    statement: &Statement<G>,
    rng: &mut Rng,
) -> ProofResult<()> {
    let msm = verify_aux(verifier_state, crs, circuit, statement, rng)?;
    let g = msm.execute();
    if g.is_zero() {
        Ok(())
    } else {
        Err(ProofError::InvalidProof)
    }
}

#[cfg(test)]
mod tests {
    use crate::circuit::types::Statement;

    use super::*;
    use ark_secp256k1::{Fr, Projective};
    use proptest::{prelude::*, test_runner::Config};
    use rand::rngs::OsRng;
    use rayon::prelude::*;
    use spongefish::codecs::arkworks_algebra::CommonGroupToUnit;

    proptest! {
        #![proptest_config(Config::with_cases(2))]
        #[test]
        fn test_circuit_proof(
           (n,q) in (prop_oneof![Just(2), Just(4), Just(8), Just(16), Just(32)], 4usize..100)
        ) {
            let mut rng = OsRng;

            let (circuit, witness) = types::Circuit::<Fr>::generate_from_witness(q, n, &mut rng);

            assert!(circuit.is_satisfied_by(&witness), "Circuit not satisfied by witness");

            let crs: types::CRS<Projective> = types::CRS::rand(circuit.dim(), &mut rng);

            let domain_separator = {
                let domain_separator = DomainSeparator::new("test-circuit-proof");
                let domain_separator = CircuitProofDomainSeparator::<Projective>::circuit_proof_statement(domain_separator, witness.v.len())
                    .ratchet();
                CircuitProofDomainSeparator::<Projective>::add_circuit_proof(domain_separator, n)
            };

            let statement: Statement<Projective> = Statement::new(&crs, &witness);

            let mut prover_state = domain_separator.to_prover_state();
            prover_state.public_points(&statement.v).unwrap();
            prover_state.ratchet().unwrap();

            let proof = prove(&mut prover_state, &crs, &circuit, &witness, &mut rng).unwrap();

            let mut verifier_state = domain_separator.to_verifier_state(&proof);
            verifier_state.public_points(&statement.v).expect("cannot add statement");
            verifier_state.ratchet().expect("failed to ratchet");

            verify(&mut verifier_state, &crs, &circuit, &statement, &mut OsRng).expect("proof should verify");
        }
    }

    proptest! {
        #![proptest_config(Config::with_cases(2))]
        #[test]
        fn test_batch_circuit_proof_verify_works(
           (n,q) in (prop_oneof![Just(2), Just(4), Just(8), Just(16)], 4usize..50)
        ) {
            let mut rng = OsRng;

            let circuits_and_witnesses = (0..4).map(|_| {
                types::Circuit::<Fr>::generate_from_witness(q, n, &mut rng)
            }).collect::<Vec<_>>();

            let crs: types::CRS<Projective> = types::CRS::rand(n, &mut rng);

            let statements = circuits_and_witnesses.iter().map(|(circuit, witness)| {
                assert!(circuit.is_satisfied_by(witness), "Circuit not satisfied by witness");
                (circuit, witness, Statement::new(&crs, witness))
            }).collect::<Vec<_>>();

            let domain_separator = {
                let domain_separator = DomainSeparator::new("test-circuit-proof-batch");
                let domain_separator = CircuitProofDomainSeparator::<Projective>::circuit_proof_statement(domain_separator.clone(), n).ratchet();
                CircuitProofDomainSeparator::<Projective>::add_circuit_proof(domain_separator, n)
            };

            let proofs = statements.par_iter().map(|(circuit, witness, statement)| {
                let mut prover_state = domain_separator.to_prover_state();
                prover_state.public_points(&statement.v)?;
                prover_state.ratchet().unwrap();
                let proof = prove(&mut prover_state, &crs, circuit, witness, &mut OsRng)?;
                Ok((circuit, statement, proof))
            }).collect::<Result<Vec<_>, ProofError>>()?;

            let verifications: Vec<Msm<Projective>> = proofs.iter().map(|(circuit, statement, proof)| {
                let mut verifier_state = domain_separator.to_verifier_state(proof);
                verifier_state.public_points(&statement.v)?;
                verifier_state.ratchet().unwrap();
                verify_aux(&mut verifier_state, &crs, circuit, statement, &mut OsRng)
            }).collect::<Result<Vec<_>, ProofError>>()?;

            let verifications = nonempty::NonEmpty::from_vec(verifications).expect("non-empty vec");

            crate::msm::verify_batch_aux(verifications, &mut OsRng).expect("should verify batch");
        }
    }
}
