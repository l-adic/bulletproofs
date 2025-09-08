use std::{iter::successors, ops::Mul};

use ark_ec::CurveGroup;
use ark_ff::{Field, One, UniformRand, Zero};
use spongefish::{
    DomainSeparator, ProofResult, ProverState, VerifierState,
    codecs::arkworks_algebra::{
        FieldDomainSeparator, FieldToUnitDeserialize, FieldToUnitSerialize, GroupDomainSeparator,
        GroupToUnitDeserialize, GroupToUnitSerialize, UnitToField,
    },
};

use crate::{
    circuit::types::Statement,
    ipa::{extended::ExtendedBulletproofDomainSeparator, types as ipa_types},
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
    let n = crs.size();
    assert!(
        n == circuit.dim(),
        "CRS size and circuit dimension must match"
    );
    let q = circuit.size();
    let [alpha, beta, rho]: [G::ScalarField; 3] =
        std::array::from_fn(|_| G::ScalarField::rand(rng));

    let a_i = crs.h.mul(alpha) + {
        let bases: Vec<G::Affine> = crs
            .ipa_crs
            .gs
            .iter()
            .chain(crs.ipa_crs.hs.iter())
            .copied()
            .collect();
        let scalars: Vec<G::ScalarField> = witness
            .a_l
            .iter()
            .chain(witness.a_r.iter())
            .copied()
            .collect();
        G::msm_unchecked(&bases, &scalars)
    };

    let a_o = crs.h.mul(beta) + G::msm_unchecked(&crs.ipa_crs.gs, &witness.a_o);

    let s_l = (0..n)
        .map(|_| G::ScalarField::rand(rng))
        .collect::<Vec<_>>();
    let s_r = (0..n)
        .map(|_| G::ScalarField::rand(rng))
        .collect::<Vec<_>>();

    let s = crs.h.mul(rho) + {
        let bases: Vec<G::Affine> = crs
            .ipa_crs
            .gs
            .iter()
            .chain(crs.ipa_crs.hs.iter())
            .copied()
            .collect();
        let scalars: Vec<G::ScalarField> = s_l.iter().chain(s_r.iter()).copied().collect();
        G::msm_unchecked(&bases, &scalars)
    };

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
        let hs_prime = create_hs_prime::<G>(&crs.ipa_crs.hs[0..n], y);

        let mut extended_statement: ipa_types::extended::Statement<G> =
            witness.extended_statement(&crs.ipa_crs);

        extended_statement.p += crs.h.mul(-mu);

        prover_state.add_scalars(&[tao_x, mu, extended_statement.c])?;

        let crs = ipa_types::CRS {
            gs: crs.ipa_crs.gs.to_vec(),
            hs: hs_prime,
            u: crs.ipa_crs.u,
        };

        crate::ipa::extended::prove(prover_state, &crs, &extended_statement, &witness)?;
    }

    Ok(prover_state.narg_string().to_vec())
}

fn create_hs_prime<G: CurveGroup>(hs: &[G::Affine], y: G::ScalarField) -> Vec<G::Affine> {
    let y_inv = y.inverse().expect("non-zero y");
    let ys_inv = std::iter::successors(Some(G::ScalarField::one()), |&x| (Some(x * y_inv)));
    G::normalize_batch(
        &hs.iter()
            .zip(ys_inv)
            .map(|(h, y_inv)| h.mul(y_inv))
            .collect::<Vec<_>>(),
    )
}

pub fn verify<G: CurveGroup>(
    verifier_state: &mut VerifierState,
    crs: &types::CRS<G>,
    circuit: &types::Circuit<G::ScalarField>,
    statement: Statement<G>,
) -> ProofResult<()> {
    let n = crs.size();
    let q = circuit.size();

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

    let delta_y_z = {
        let v = mat_mul_l(&z_vec, &circuit.w_r);
        let l = y_inv_vec.iter().copied().hadamard(v);
        let r = mat_mul_l(&z_vec, &circuit.w_l);
        inner_product(l, r)
    };

    {
        let lhs = crs.g.mul(t_hat) + crs.h.mul(tao_x);

        let rhs = crs.g.mul(
            x.square()
                * (delta_y_z + inner_product(z_vec.iter().copied(), circuit.c.iter().copied())),
        ) + {
            let scalars = mat_mul_l(&z_vec, &circuit.w_v)
                .map(|zi| x.square() * zi)
                .collect::<Vec<_>>();
            G::msm_unchecked(&G::normalize_batch(&statement.v), &scalars)
        } + {
            tts.iter()
                .enumerate()
                .filter_map(|(i, tt_i_opt)| tt_i_opt.map(|tt_i| tt_i.mul(x.pow([i as u64 + 1]))))
                .fold(G::zero(), |acc, val| acc + val)
        };
        assert!((lhs - rhs).is_zero(), "Failed to verify t_hat = t(x)");
    };
    {
        let hs_prime = create_hs_prime::<G>(&crs.ipa_crs.hs[0..n], y);

        let ww_l = G::msm_unchecked(
            &hs_prime,
            &mat_mul_l(&z_vec, &circuit.w_l).collect::<Vec<_>>(),
        );
        let ww_r = {
            let v = mat_mul_l(&z_vec, &circuit.w_r);
            let scalars = y_inv_vec.iter().copied().hadamard(v).collect::<Vec<_>>();
            G::msm_unchecked(&crs.ipa_crs.gs, &scalars)
        };
        let ww_o = G::msm_unchecked(
            &hs_prime,
            &mat_mul_l(&z_vec, &circuit.w_o).collect::<Vec<_>>(),
        );

        let neg_y_vec = y_vec.iter().map(|yi| -*yi).collect::<Vec<_>>();

        let p: G = a_i.mul(x)
            + a_o.mul(x.square())
            + G::msm_unchecked(&hs_prime, &neg_y_vec)
            + ww_l.mul(x)
            + ww_r.mul(x)
            + ww_o
            + s.mul(x.pow([3]));

        let p_with_mu = p + crs.h.mul(-mu);

        let extended_statement = ipa_types::extended::Statement {
            p: p_with_mu,
            c: t_hat,
        };

        let crs = ipa_types::CRS {
            gs: crs.ipa_crs.gs.to_vec(),
            hs: hs_prime,
            u: crs.ipa_crs.u,
        };
        crate::ipa::extended::verify(verifier_state, &crs, &extended_statement)
    }?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::circuit::types::Statement;

    use super::*;
    use ark_secp256k1::{Fr, Projective};
    use proptest::{prelude::*, test_runner::Config};
    use rand::rngs::OsRng;
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

            verify(&mut verifier_state, &crs, &circuit, statement).expect("proof should verify");
        }
    }
}
