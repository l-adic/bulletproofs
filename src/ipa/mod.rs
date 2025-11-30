pub mod extended;
pub mod types;

use crate::BulletproofResult;
use crate::{
    ipa::types::{CRS, Statement, Witness},
    msm::Msm,
    vector_ops::{VectorOps, inner_product},
};
use ark_ec::{CurveGroup, PrimeGroup};
use ark_ff::{Field, One, batch_inversion};
use ark_std::log2;
use rayon::prelude::*;
use spongefish::{Codec, Encoding, NargDeserialize, ProverState, VerifierState};
use std::ops::Mul;
use tracing::instrument;

#[instrument(skip_all, fields(witness_size = witness.a.len()), level = "debug")]
pub fn prove<G: CurveGroup + Encoding>(
    prover_state: &mut ProverState,
    crs: &CRS<G>,
    mut statement: Statement<G>,
    witness: &Witness<G>,
) -> Vec<u8>
where
    <G as PrimeGroup>::ScalarField: Codec,
{
    let mut n = witness.size();
    let mut gs: Vec<<G as CurveGroup>::Affine> = crs.gs[0..n].to_vec();
    let mut hs: Vec<<G as CurveGroup>::Affine> = crs.hs[0..n].to_vec();
    let mut witness = witness.clone();

    while n != 1 {
        n /= 2;
        let (g_left, g_right) = gs.split_at(n);
        let (h_left, h_right) = hs.split_at(n);
        let (a_left, a_right) = witness.a.split_at(n);
        let (b_left, b_right) = witness.b.split_at(n);

        let (left, right) = rayon::join(
            || {
                let c_left = inner_product(a_left.iter().copied(), b_right.iter().copied());
                crs.u.mul(c_left) + {
                    let bases: Vec<G::Affine> = g_right
                        .iter()
                        .copied()
                        .chain(h_left.iter().copied())
                        .collect();
                    let scalars: Vec<G::ScalarField> = a_left
                        .iter()
                        .copied()
                        .chain(b_right.iter().copied())
                        .collect();
                    G::msm_unchecked(&bases, &scalars)
                }
            },
            || {
                let c_right = inner_product(a_right.iter().copied(), b_left.iter().copied());
                crs.u.mul(c_right) + {
                    let bases: Vec<G::Affine> = g_left
                        .iter()
                        .copied()
                        .chain(h_right.iter().copied())
                        .collect();
                    let scalars: Vec<G::ScalarField> = a_right
                        .iter()
                        .copied()
                        .chain(b_left.iter().copied())
                        .collect();
                    G::msm_unchecked(&bases, &scalars)
                }
            },
        );

        prover_state.prover_message(&[left, right]);

        let alpha: G::ScalarField = prover_state.verifier_message();
        let alpha_inv = alpha.inverse().expect("non-zero alpha");

        let (new_gs, new_hs) = rayon::join(
            || fold_generators::<G>(g_left, g_right, alpha_inv, alpha),
            || fold_generators::<G>(h_left, h_right, alpha, alpha_inv),
        );
        gs = new_gs;
        hs = new_hs;

        let (new_a, new_b) = rayon::join(
            || fold_scalars(a_left, a_right, alpha, alpha_inv),
            || fold_scalars(b_left, b_right, alpha_inv, alpha),
        );
        witness.a = new_a;
        witness.b = new_b;

        statement.p += left * alpha.square() + right * alpha_inv.square();
    }

    prover_state.prover_messages(&[witness.a[0], witness.b[0]]);
    prover_state.narg_string().to_vec()
}

#[instrument(skip_all, fields(crs_size = crs.size()), level = "debug")]
pub fn verify_aux<G: CurveGroup + Encoding + NargDeserialize>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
) -> BulletproofResult<Msm<G>>
where
    G::ScalarField: Codec,
{
    let n = statement.witness_size;
    let log2_n = log2(n as usize) as usize;

    let transcript = (0..log2_n)
        .map(|_| {
            let [left, right]: [G; 2] = verifier_state.prover_message()?;
            let x: G::ScalarField = verifier_state.verifier_message();
            Ok(((left, right), x))
        })
        .collect::<BulletproofResult<Vec<_>>>()?;

    let mut msm = Msm::new();

    {
        let [a, b]: [G::ScalarField; 2] = verifier_state.prover_messages()?;
        msm.upsert(crs.u, a * b);

        let challenge_powers: Vec<G::ScalarField> = transcript.iter().map(|&(_, x)| x).collect();
        let challenge_inverses = {
            let mut inverses = challenge_powers.clone();
            batch_inversion(&mut inverses);
            inverses
        };

        let ss: Vec<G::ScalarField> = (0..n)
            .into_par_iter()
            .map(|i| {
                (0..log2_n)
                    .map(|j| {
                        let idx = log2_n - j - 1;
                        if (i >> j) & 1 == 1 {
                            challenge_powers[idx]
                        } else {
                            challenge_inverses[idx]
                        }
                    })
                    .product()
            })
            .collect();

        let ss_inverse = {
            let mut ss_inverse = ss.clone();
            batch_inversion(&mut ss_inverse);
            ss_inverse
        };

        msm.upsert_batch(
            crs.gs[0..(n as usize)]
                .iter()
                .copied()
                .zip(ss.into_iter().scale(a)),
        );
        msm.upsert_batch(
            crs.hs[0..(n as usize)]
                .iter()
                .copied()
                .zip(ss_inverse.into_iter().scale(b)),
        );
    };

    {
        let mut bases: Vec<G> = {
            let mut v = Vec::with_capacity(2 * log2_n + 1);
            v.push(statement.p);
            v
        };
        let mut scalars: Vec<G::ScalarField> = {
            let mut v = Vec::with_capacity(2 * log2_n + 1);
            v.push(G::ScalarField::one());
            v
        };
        transcript.into_iter().for_each(|((left, right), x)| {
            bases.push(left);
            scalars.push(x.square());
            bases.push(right);
            scalars.push(x.inverse().expect("non-zero inverse").square());
        });
        let bases: Vec<G::Affine> = G::normalize_batch(&bases);
        scalars = scalars.into_iter().scale(-G::ScalarField::one()).collect();
        msm.upsert_batch(bases.into_iter().zip(scalars));
    };

    Ok(msm)
}

#[instrument(skip_all, fields(crs_size = crs.size()), level = "debug")]
pub fn verify<G: CurveGroup + Encoding + NargDeserialize>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
) -> BulletproofResult<()>
where
    G::ScalarField: Codec,
{
    let proof = verify_aux(verifier_state, crs, statement)?;
    let (bases, scalars) = proof.bases_and_scalars();
    let g = G::msm_unchecked(&bases, &scalars);
    if g.is_zero() {
        Ok(())
    } else {
        Err(crate::VerificationError)
    }
}

#[instrument(skip_all, fields(size = left.len()), level = "debug")]
fn fold_generators<G: CurveGroup>(
    left: &[G::Affine],
    right: &[G::Affine],
    x: G::ScalarField,
    y: G::ScalarField,
) -> Vec<G::Affine> {
    let gs: Vec<G> = left
        .par_iter()
        .zip(right)
        .map(|(l, r)| l.mul(x) + r.mul(y))
        .collect();
    G::normalize_batch(&gs)
}

fn fold_scalars<Fr: Field>(left: &[Fr], right: &[Fr], x: Fr, y: Fr) -> Vec<Fr> {
    left.par_iter()
        .zip(right)
        .map(|(l, r)| *l * x + *r * y)
        .collect::<Vec<_>>()
}

#[cfg(test)]
mod tests_proof {
    use super::*;
    use crate::ipa::types::{self as ipa_types, CrsSize};
    use crate::msm::verify_batch_aux;
    use ark_vesta::{self, Projective};
    use nonempty::NonEmpty;
    use proptest::{prelude::*, test_runner::Config};
    use rand::rngs::OsRng;

    proptest! {
      #![proptest_config(Config::with_cases(2))]
      #[test]
      fn test_prove_verify_works((crs, witness) in any::<CrsSize>().prop_map(|crs_size| {
          let mut rng = OsRng;
          let crs: CRS<Projective> = CRS::rand(crs_size, &mut rng);
          let n = crs.size() as u64;
          let witness: Witness<Projective> = Witness::rand(n, &mut rng);
          (crs, witness)
      })) {

            {

              let instance = witness.statement(&crs);

              let domain_separator =
                  spongefish::domain_separator!("bulletproofs")
                      .instance(&instance);

              let mut prover_state = domain_separator.std_prover();
              let narg_string = prove(&mut prover_state, &crs, instance, &witness);

              let mut verifier_state = domain_separator.std_verifier(&narg_string);
              verify(&mut verifier_state, &crs, &instance).expect("Invalid proof")

            }

            {
                let statement: ipa_types::extended::Statement<Projective> = witness.extended_statement(&crs);

                let domain_separator =
                    spongefish::domain_separator!("test-ipa-extended")
                        .instance(&statement);

                let mut prover_state = domain_separator.std_prover();
                let proof = crate::ipa::extended::prove(&mut prover_state, &crs, &statement, &witness);

                let mut verifier_state = domain_separator.std_verifier(&proof);
                crate::ipa::extended::verify(&mut verifier_state, &crs, &statement).expect("proof should verify");
            }

      }
    }

    proptest! {
      #![proptest_config(Config::with_cases(2))]
      #[test]
      fn test_batch_prove_verify_works((crs, witnesses, _witness_size) in any::<CrsSize>().prop_map(|crs_size| {
          let mut rng = OsRng;
          let crs: CRS<Projective> = CRS::rand(crs_size, &mut rng);
          let n = crs.size() as u64;
          let witness_size = n as usize;
          let witnesses = (0..4).map(|_| Witness::rand(n, &mut rng)).collect::<Vec<_>>();
          (crs, witnesses, witness_size)
      })) {

        let statements = witnesses.iter().map(|w| (w, w.statement(&crs))).collect::<Vec<_>>();

        let proofs = statements.par_iter().map(|(witness, statement)| {
            let domain_separator =
                spongefish::domain_separator!("test-ipa-batch")
                    .instance(statement);

            let mut prover_state = domain_separator.std_prover();
            let narg_string = prove(&mut prover_state, &crs, *statement, witness);
            (*statement, narg_string)
        }).collect::<Vec<_>>();

        let verifications: Vec<Msm<Projective>> = proofs.iter().map(|(statement, narg_string)| {
            let domain_separator =
                spongefish::domain_separator!("test-ipa-batch")
                    .instance(statement);

            let mut verifier_state = domain_separator.std_verifier(narg_string);
            verify_aux(&mut verifier_state, &crs, statement).expect("verify_aux should succeed")
        }).collect::<Vec<_>>();

        let verifications = NonEmpty::from_vec(verifications).expect("non-empty vec");

        verify_batch_aux(verifications, &mut OsRng).expect("should verify batch");
      }
    }
}
