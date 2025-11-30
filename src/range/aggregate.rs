use crate::BulletproofResult;
use ark_ec::{CurveGroup, PrimeGroup};
use ark_ff::{Field, One, UniformRand, Zero};
use spongefish::{Codec, Encoding, NargDeserialize, ProverState};
use std::{iter::successors, ops::Mul};
use tracing::instrument;

use crate::vector_ops::{VectorOps, sum};
use crate::{
    ipa::{self, types as ipa_types},
    range::types::aggregate::{Statement, Witness},
};
use crate::{
    msm::Msm,
    range::{
        types::{CRS, VectorPolynomial},
        utils::{bit_decomposition, create_hs_prime},
    },
    vector_ops::inner_product,
};

#[instrument(skip_all, fields(n_bits = witness.n_bits, m = witness.len()), level = "debug")]
pub fn prove<G: CurveGroup + Encoding, Rng: rand::Rng>(
    mut prover_state: ProverState,
    crs: &CRS<G>,
    witness: &Witness<G::ScalarField>,
    rng: &mut Rng,
) -> Vec<u8>
where
    <G as PrimeGroup>::ScalarField: Codec,
{
    let n_bits = witness.n_bits;
    let m = witness.len();

    assert!(
        crs.size() >= (n_bits as usize) * m,
        "CRS size is smaller than witness n_bits * m"
    );

    let gs = &crs.ipa_crs.gs[0..(n_bits as usize) * m];
    let hs = &crs.ipa_crs.hs[0..(n_bits as usize) * m];

    let one_vec = vec![G::ScalarField::one(); (n_bits as usize) * m];
    let two_vec: Vec<G::ScalarField> = successors(Some(G::ScalarField::one()), |succ| {
        Some(*succ * G::ScalarField::from(2u64))
    })
    .take(n_bits as usize)
    .collect();

    let a_l: Vec<G::ScalarField> = {
        let mut res = Vec::with_capacity((n_bits as usize) * m);
        witness.v.iter().for_each(|val| {
            let mut bits = bit_decomposition(*val);
            bits.resize(n_bits as usize, G::ScalarField::zero());
            res.extend(bits);
        });
        res
    };

    let a_r: Vec<G::ScalarField> = a_l
        .iter()
        .copied()
        .vector_sub(one_vec.iter().copied())
        .collect();

    let alpha: G::ScalarField = UniformRand::rand(rng);
    let rho: G::ScalarField = UniformRand::rand(rng);
    let s_l: Vec<G::ScalarField> = (0..(n_bits as usize) * m)
        .map(|_| UniformRand::rand(rng))
        .collect();
    let s_r: Vec<G::ScalarField> = (0..(n_bits as usize) * m)
        .map(|_| UniformRand::rand(rng))
        .collect();

    let (a, s) = {
        let bases: Vec<G::Affine> = gs.iter().chain(hs.iter()).copied().collect();
        let a_scalars: Vec<G::ScalarField> = a_l.iter().chain(a_r.iter()).copied().collect();
        let s_scalars: Vec<G::ScalarField> = s_l.iter().chain(s_r.iter()).copied().collect();

        rayon::join(
            || crs.h.mul(alpha) + G::msm_unchecked(&bases, &a_scalars),
            || crs.h.mul(rho) + G::msm_unchecked(&bases, &s_scalars),
        )
    };
    prover_state.prover_messages(&[a, s]);
    let [y, z]: [G::ScalarField; 2] = prover_state.verifier_messages();

    let y_vec: Vec<G::ScalarField> =
        successors(Some(G::ScalarField::one()), |succ| Some(*succ * y))
            .take((n_bits as usize) * m)
            .collect();

    let l_poly = {
        let coeffs = vec![
            a_l.into_iter()
                .vector_sub(one_vec.iter().copied().scale(z))
                .collect(),
            s_l.clone(),
        ];
        VectorPolynomial::new(coeffs, (n_bits as usize) * m)
    };

    let r_poly = {
        let coeffs = vec![
            y_vec
                .iter()
                .copied()
                .hadamard(a_r.into_iter().vector_add(one_vec.into_iter().scale(z)))
                .vector_add({
                    let z_powers = successors(Some(z.square()), |&z_pow| Some(z_pow * z)).take(m);
                    z_powers
                        .flat_map(|z_power| std::iter::repeat_n(z_power, n_bits as usize))
                        .hadamard(two_vec.iter().cycle().take((n_bits as usize) * m).copied())
                })
                .collect(),
            y_vec.into_iter().hadamard(s_r.into_iter()).collect(),
        ];
        VectorPolynomial::new(coeffs, (n_bits as usize) * m)
    };

    let tao1: G::ScalarField = UniformRand::rand(rng);
    let tao2: G::ScalarField = UniformRand::rand(rng);

    {
        let t_poly = l_poly.inner_product(&r_poly);
        let tt1 = crs.g.mul(t_poly[1]) + crs.h.mul(tao1);
        let tt2 = crs.g.mul(t_poly[2]) + crs.h.mul(tao2);

        prover_state.prover_messages(&[tt1, tt2]);
    }

    {
        let x: G::ScalarField = prover_state.verifier_message();

        let tao_x = {
            let sigma_summand = {
                let z_vec = successors(Some(z.square()), |succ| Some(*succ * z)).take(m);
                inner_product(z_vec, witness.gamma.iter().copied())
            };
            tao1 * x + tao2 * x.square() + sigma_summand
        };
        let mu = alpha + rho * x;
        let l: Vec<G::ScalarField> = l_poly.evaluate(x);
        let r: Vec<G::ScalarField> = r_poly.evaluate(x);

        let witness = ipa_types::Witness::new(l, r);

        let hs_prime = G::normalize_batch(
            &create_hs_prime::<G>(hs, y)
                .into_iter()
                .map(|(h, y_inv_i)| h.mul(y_inv_i))
                .collect::<Vec<_>>(),
        );

        let mut extended_statement = witness.extended_statement(&crs.ipa_crs);

        extended_statement.p += crs.h.mul(-mu);

        prover_state.prover_messages(&[tao_x, mu, extended_statement.c]);
        let crs = ipa_types::CRS {
            gs: gs.to_vec(),
            hs: hs_prime,
            u: crs.ipa_crs.u,
        };

        ipa::extended::prove(&mut prover_state, &crs, &extended_statement, &witness);
    }

    prover_state.narg_string().to_vec()
}

#[instrument(skip_all, fields(nbits = statement.n_bits), level = "debug")]
pub fn verify_aux<G: CurveGroup + Encoding + NargDeserialize, Rng: rand::Rng>(
    verifier_state: &mut spongefish::VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
    rng: &mut Rng,
) -> BulletproofResult<Msm<G>>
where
    <G as PrimeGroup>::ScalarField: Codec,
{
    let n_bits = statement.n_bits;
    let m = statement.v.len();

    let [a, s]: [G; 2] = verifier_state.prover_messages()?;
    let [y, z]: [G::ScalarField; 2] = [
        verifier_state.verifier_message(),
        verifier_state.verifier_message(),
    ];
    let [tt1, tt2]: [G; 2] = verifier_state.prover_messages()?;
    let x: G::ScalarField = verifier_state.verifier_message();
    let [tao_x, mu, t_hat]: [G::ScalarField; 3] = verifier_state.prover_messages()?;

    let two_vec: Vec<G::ScalarField> = successors(Some(G::ScalarField::one()), |succ| {
        Some(*succ * G::ScalarField::from(2u64))
    })
    .take(n_bits as usize)
    .collect();
    let y_vec: Vec<G::ScalarField> =
        successors(Some(G::ScalarField::one()), |succ| Some(*succ * y))
            .take((n_bits as usize) * m)
            .collect();

    let (g, msm) = rayon::join(
        || {
            let tt1 = tt1.into_affine();
            let tt2 = tt2.into_affine();

            let sigma_summand: G::ScalarField = {
                let d = sum(two_vec.iter().copied());
                let z_vec = successors(Some(z.square() * z), |succ| Some(*succ * z)).take(m);
                sum(z_vec) * d
            };

            let delta_y_z = { (z - z.square()) * sum(y_vec.iter().copied()) - sigma_summand };

            let z_vec = {
                successors(Some(z.square()), |succ| Some(*succ * z))
                    .take(m)
                    .collect::<Vec<_>>()
            };

            let vs = G::normalize_batch(&statement.v);

            crs.g.mul(t_hat - delta_y_z) + crs.h.mul(tao_x)
                - (G::msm_unchecked(&vs, &z_vec) + tt1.mul(x) + tt2.mul(x.square()))
        },
        || {
            let gs = &crs.ipa_crs.gs[0..(n_bits as usize) * m];
            let hs = &crs.ipa_crs.hs[0..(n_bits as usize) * m];
            let scaled_hs = create_hs_prime::<G>(hs, y);
            let hs_prime = G::normalize_batch(
                &scaled_hs
                    .iter()
                    .map(|(h, y_inv_i)| h.mul(y_inv_i))
                    .collect::<Vec<_>>(),
            );

            let p: G = {
                let gs_scalars = std::iter::repeat_n(-z, (n_bits as usize) * m);

                let hs_combined_scalars = {
                    // Base term: z * y_vec[i] for each position i
                    let base_terms = y_vec.iter().copied().scale(z);

                    // Sigma term: same pattern as prover's sigma_sum
                    let sigma_terms = successors(Some(z.square()), |&z_pow| Some(z_pow * z))
                        .take(m)
                        .flat_map(|z_power| two_vec.iter().copied().scale(z_power));

                    base_terms.vector_add(sigma_terms)
                };

                {
                    let bases: Vec<G::Affine> =
                        gs.iter().copied().chain(hs_prime.iter().copied()).collect();
                    let scalars: Vec<G::ScalarField> =
                        gs_scalars.chain(hs_combined_scalars).collect();
                    a + s.mul(x) + G::msm_unchecked(&bases, &scalars)
                }
            };

            let extended_statement = ipa_types::extended::Statement {
                p: p + crs.h.mul(-mu),
                c: t_hat,
                witness_size: n_bits * (m as u64),
            };

            let mut msm =
                ipa::extended::verify_aux(verifier_state, &crs.ipa_crs, &extended_statement)?;

            msm.scale_elems(scaled_hs.into_iter());
            Ok::<_, crate::VerificationError>(msm)
        },
    );
    let mut msm = msm?;

    let alpha = G::ScalarField::rand(rng);
    msm.upsert(g.into_affine(), alpha);

    Ok(msm)
}

#[instrument(skip_all, fields(nbits = statement.n_bits), level = "debug")]
pub fn verify<G: CurveGroup + Encoding + NargDeserialize, Rng: rand::Rng>(
    verifier_state: &mut spongefish::VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
    rng: &mut Rng,
) -> BulletproofResult<()>
where
    <G as PrimeGroup>::ScalarField: Codec,
{
    let msm = verify_aux(verifier_state, crs, statement, rng)?;
    let g = msm.execute();
    if g.is_zero() {
        Ok(())
    } else {
        Err(crate::VerificationError)
    }
}
#[cfg(test)]
mod tests_range {
    use crate::msm::verify_batch_aux;

    use super::*;
    use ark_secp256k1::{Fr, Projective};
    use nonempty::NonEmpty;
    use proptest::{prelude::*, test_runner::Config};
    use rand::rngs::OsRng;
    use rayon::prelude::*;

    proptest! {
          #![proptest_config(Config::with_cases(2))]
          #[test]
        fn test_aggregated_range_proof(
            n_bits in prop_oneof![Just(16), Just(32), Just(64)],
            m in prop_oneof![Just(2usize), Just(4), Just(8), Just(16), Just(32), Just(64), Just(128), Just(256), Just(512)]
        ) {

            let mut rng = OsRng;
            let crs: CRS<Projective> = CRS::rand((n_bits as usize) * m, &mut rng);

            // Generate m random values in range [0, 2^n_bits)
            let max_value = (1u128 << n_bits.min(127)) - 1;
            let v: Vec<Fr> = (0..m)
                .map(|_| Fr::from(rand::Rng::gen_range(&mut rng, 0u128..=max_value)))
                .collect();

            let witness = Witness::<Fr>::new(v, n_bits, &mut rng);
            let statement = Statement::new(&crs, &witness);

            let domain_separator = spongefish::domain_separator!("test-aggregated-range-proof")
                .instance(&statement.v);

            let prover_state = domain_separator.std_prover();
            let proof = prove(prover_state, &crs, &witness, &mut rng);

            tracing::info!("proof size: {} bytes", proof.len());

            let mut verifier_state = domain_separator.std_verifier(&proof);
            verify(&mut verifier_state, &crs, &statement, &mut rng).expect("proof should verify")
        }
    }

    proptest! {
      #![proptest_config(Config::with_cases(2))]
      #[test]
      fn test_batch_aggregated_range_proof_verify_works(
          n_bits in prop_oneof![Just(8u64), Just(16), Just(32)],
          m in prop_oneof![Just(2usize), Just(4), Just(8), Just(16)]
      ) {

        let mut rng = OsRng;
        let crs: CRS<Projective> = CRS::rand((n_bits as usize) * m, &mut rng);

        let witnesses = (0..4).map(|_| {
            let max_value = (1u128 << n_bits.min(127)) - 1;
            let v: Vec<Fr> = (0..m)
                .map(|_| Fr::from(rand::Rng::gen_range(&mut rng, 0u128..=max_value)))
                .collect();
            Witness::<Fr>::new(v, n_bits, &mut rng)
        }).collect::<Vec<_>>();

        let statements = witnesses.iter().map(|w| (w, Statement::new(&crs, w))).collect::<Vec<_>>();

        let proofs = statements.par_iter().map(|(witness, statement)| {
            let domain_separator = spongefish::domain_separator!("test-aggregated-range-proof-batch")
                .instance(&statement.v);
            let prover_state = domain_separator.std_prover();
            let proof = prove(prover_state, &crs, witness, &mut OsRng);
            Ok((statement, proof))
        }).collect::<Result<Vec<_>, crate::VerificationError>>().unwrap();

        let verifications: Vec<Msm<Projective>> = proofs.iter().map(|(statement, proof)| {
            let domain_separator = spongefish::domain_separator!("test-aggregated-range-proof-batch")
                .instance(&statement.v);
            let mut verifier_state = domain_separator.std_verifier(proof);
            verify_aux(&mut verifier_state, &crs, statement, &mut OsRng)
        }).collect::<Result<Vec<_>, crate::VerificationError>>().unwrap();

        let verifications = NonEmpty::from_vec(verifications).expect("non-empty vec");

        verify_batch_aux(verifications, &mut OsRng).expect("should verify batch");
      }
    }
}
