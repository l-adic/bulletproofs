pub mod extended;
pub mod types;

use crate::{
    ipa::types::{CRS, Statement, Witness},
    vector_ops::{VectorOps, inner_product},
};
use ark_ec::CurveGroup;
use ark_ff::{Field, One, UniformRand, batch_inversion};
use ark_std::log2;
use nonempty::NonEmpty;
use rayon::prelude::*;
use spongefish::{
    DomainSeparator, ProofError, ProofResult, ProverState, VerifierState,
    codecs::arkworks_algebra::{
        FieldDomainSeparator, FieldToUnitDeserialize, FieldToUnitSerialize, GroupDomainSeparator,
        GroupToUnitDeserialize, GroupToUnitSerialize, UnitToField,
    },
};
use std::{iter::successors, ops::Mul};
use tracing::instrument;

pub trait BulletproofDomainSeparator<G: CurveGroup> {
    fn bulletproof_statement(self) -> Self;
    fn add_bulletproof(self, len: usize) -> Self;
}

impl<G> BulletproofDomainSeparator<G> for DomainSeparator
where
    G: CurveGroup,
    Self: GroupDomainSeparator<G> + FieldDomainSeparator<G::ScalarField>,
{
    /// The IO of the bulletproof statement
    fn bulletproof_statement(self) -> Self {
        self.add_points(1, "Pedersen commitment")
    }

    /// The IO of the bulletproof protocol
    fn add_bulletproof(mut self, len: usize) -> Self {
        for _ in 0..log2(len) {
            self = self
                .add_points(2, "round-message")
                .challenge_scalars(1, "challenge");
        }
        self.add_scalars(2, "final-message")
    }
}

#[instrument(skip_all, fields(witness_size = witness.a.len()), level = "debug")]
pub fn prove<G: CurveGroup>(
    prover_state: &mut ProverState,
    crs: &CRS<G>,
    mut statement: Statement<G>,
    witness: &Witness<G>,
) -> ProofResult<Vec<u8>> {
    let mut n = crs.size();
    let mut gs = crs.gs.clone();
    let mut hs = crs.hs.clone();
    let mut witness = witness.clone();

    while n != 1 {
        n /= 2;
        let (g_left, g_right) = gs.split_at(n);
        let (h_left, h_right) = hs.split_at(n);
        let (a_left, a_right) = witness.a.split_at(n);
        let (b_left, b_right) = witness.b.split_at(n);

        let left = {
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
        };

        let right = {
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
        };

        prover_state.add_points(&[left, right])?;

        let [alpha]: [G::ScalarField; 1] = prover_state.challenge_scalars()?;
        let alpha_inv = alpha.inverse().expect("non-zero alpha");

        gs = fold_generators::<G>(g_left, g_right, alpha_inv, alpha);
        hs = fold_generators::<G>(h_left, h_right, alpha, alpha_inv);

        witness.a = fold_scalars(a_left, a_right, alpha, alpha_inv);
        witness.b = fold_scalars(b_left, b_right, alpha_inv, alpha);

        statement.p += left * alpha.square() + right * alpha_inv.square();
    }

    prover_state.add_scalars(&[witness.a[0], witness.b[0]])?;
    Ok(prover_state.narg_string().to_vec())
}

pub struct ProverMSM<G: CurveGroup> {
    bases: Vec<G::Affine>,
    scalars: Vec<G::ScalarField>,
}

#[instrument(skip_all, fields(n_proofs = proofs.len()), level = "debug")]
pub fn verify_batch_aux<G: CurveGroup, Rng: rand::Rng>(
    proofs: NonEmpty<ProverMSM<G>>,
    rng: &mut Rng,
) -> ProofResult<()> {
    let alpha = G::ScalarField::rand(rng);
    let powers_of_alpha = successors(Some(G::ScalarField::one()), |state| Some(*state * alpha));
    let bases = proofs
        .iter()
        .flat_map(|proof| proof.bases.iter().copied())
        .collect::<Vec<_>>();
    let scalars = proofs
        .into_iter()
        .zip(powers_of_alpha)
        .flat_map(|(proof, alpha_i)| {
            proof
                .scalars
                .iter()
                .map(|s| *s * alpha_i)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    if G::msm_unchecked(&bases, &scalars).is_zero() {
        Ok(())
    } else {
        Err(ProofError::InvalidProof)
    }
}

#[instrument(skip_all, fields(crs_size = crs.size()), level = "debug")]
fn verify_aux<G: CurveGroup>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
) -> ProofResult<ProverMSM<G>> {
    let n = crs.size();
    let log2_n = log2(n) as usize;

    let transcript: Vec<((G, G), G::ScalarField)> = (0..log2_n)
        .map(|_| {
            let [left, right]: [G; 2] = verifier_state.next_points()?;
            let [x]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
            Ok(((left, right), x))
        })
        .collect::<ProofResult<Vec<_>>>()?;

    let lhs = {
        let [a, b]: [G::ScalarField; 2] = verifier_state.next_scalars()?;

        let ss: Vec<G::ScalarField> = (0..n)
            .map(|i| {
                (0..log2_n)
                    .map(|j| {
                        if (i >> j) & 1 == 1 {
                            transcript[log2_n - j - 1].1
                        } else {
                            transcript[log2_n - j - 1]
                                .1
                                .inverse()
                                .expect("non-zero inverse")
                        }
                    })
                    .fold(G::ScalarField::one(), |acc, x| acc * x)
            })
            .collect::<Vec<_>>();

        let ss_inverse = {
            let mut ss_inverse = ss.clone();
            batch_inversion(&mut ss_inverse);
            ss_inverse
        };
        let mut bases = Vec::with_capacity(1 + 2 * n);
        let mut scalars = Vec::with_capacity(1 + 2 * n);

        bases.push(crs.u);
        scalars.push(a * b);

        bases.extend(crs.gs.iter().chain(crs.hs.iter()).copied());
        scalars.extend(
            ss.iter()
                .copied()
                .scale(a)
                .chain(ss_inverse.iter().copied().scale(b)),
        );

        (bases, scalars)
    };

    let negative_rhs = {
        let mut bases: Vec<G> = {
            let mut v = Vec::with_capacity(log2_n);
            v.push(statement.p);
            v
        };
        let mut scalars: Vec<G::ScalarField> = {
            let mut v = Vec::with_capacity(log2_n);
            v.push(-G::ScalarField::one());
            v
        };
        transcript.into_iter().for_each(|((left, right), x)| {
            bases.push(left);
            scalars.push(-(x.square()));
            bases.push(right);
            scalars.push(-(x.inverse().expect("non-zero inverse").square()));
        });
        (G::normalize_batch(&bases), scalars)
    };

    let res = ProverMSM {
        bases: lhs
            .0
            .iter()
            .chain(negative_rhs.0.iter())
            .copied()
            .collect::<Vec<_>>(),
        scalars: lhs
            .1
            .iter()
            .chain(negative_rhs.1.iter())
            .copied()
            .collect::<Vec<_>>(),
    };

    Ok(res)
}

#[instrument(skip_all, fields(crs_size = crs.size()), level = "debug")]
pub fn verify<G: CurveGroup>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
) -> ProofResult<()> {
    let proof = verify_aux(verifier_state, crs, statement)?;
    let g = G::msm_unchecked(&proof.bases, &proof.scalars);
    if g.is_zero() {
        Ok(())
    } else {
        Err(ProofError::InvalidProof)
    }
}

#[instrument(skip_all, fields(size = left.len()), level = "debug")]
pub(super) fn fold_generators<G: CurveGroup>(
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

pub(super) fn fold_scalars<Fr: Field>(left: &[Fr], right: &[Fr], x: Fr, y: Fr) -> Vec<Fr> {
    left.par_iter()
        .zip(right)
        .map(|(l, r)| *l * x + *r * y)
        .collect::<Vec<_>>()
}

#[cfg(test)]
mod tests_proof {
    use super::*;
    use crate::ipa::extended::ExtendedBulletproofDomainSeparator;
    use crate::ipa::types::{self as ipa_types, CrsSize};
    use ark_secp256k1::{self, Projective};
    use proptest::{prelude::*, test_runner::Config};
    use rand::rngs::OsRng;
    use spongefish::DomainSeparator;
    use spongefish::codecs::arkworks_algebra::{CommonFieldToUnit, CommonGroupToUnit};
    use tracing::info;

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

          info!("Testing prove/verify with protocol (3)");
          {
            let domain_separator = {
              let domain_separator = DomainSeparator::new("test-ipa");
              let domain_separator =
                  BulletproofDomainSeparator::<Projective>::bulletproof_statement(domain_separator).ratchet();
              BulletproofDomainSeparator::<Projective>::add_bulletproof(domain_separator, crs.size())
            };

            let mut prover_state = domain_separator.to_prover_state();

            let statement = witness.statement(&crs);
            prover_state.public_points(&[statement.p]).unwrap();
            prover_state.ratchet().unwrap();

            let proof = prove(&mut prover_state, &crs, statement, &witness).expect("proof should be generated");

            let mut fast_verifier_state = domain_separator.to_verifier_state(&proof);
            fast_verifier_state.public_points(&[statement.p]).expect("cannot add statment");
            fast_verifier_state.ratchet().expect("failed to ratchet");
            verify(&mut fast_verifier_state, &crs, &statement).expect("proof should verify");
          }

          info!("Testing prove/verify with protocol (2)");
          {

            let domain_separator = {
              let domain_separator = DomainSeparator::new("test-ipa");
              // add the IO of the bulletproof statement
              let domain_separator =
                  ExtendedBulletproofDomainSeparator::<Projective>::extended_bulletproof_statement(domain_separator).ratchet();
              // add the IO of the bulletproof protocol (the transcript)
              ExtendedBulletproofDomainSeparator::<Projective>::add_extended_bulletproof(domain_separator, crs.size())
            };

            let statement: ipa_types::extended::Statement<Projective> = witness.extended_statement(&crs);
            let mut prover_state = domain_separator.to_prover_state();
            prover_state.public_points(&[statement.p]).unwrap();
            prover_state.public_scalars(&[statement.c]).unwrap();
            prover_state.ratchet().unwrap();
            let proof = extended::prove(&mut prover_state, &crs, &statement, &witness).expect("proof should be generated");

            let mut verifier_state = domain_separator.to_verifier_state(&proof);
            verifier_state.public_points(&[statement.p]).expect("cannot add statment");
            verifier_state.public_scalars(&[statement.c]).expect("cannot add statment");
            verifier_state.ratchet().expect("failed to ratchet");
            extended::verify(&mut verifier_state, &crs, &statement).expect("proof should verify");

          }

      }
    }

    proptest! {
      #![proptest_config(Config::with_cases(2))]
      #[test]
      fn test_batch_prove_verify_works((crs, witness) in any::<CrsSize>().prop_map(|crs_size| {
          let mut rng = OsRng;
          let crs: CRS<Projective> = CRS::rand(crs_size, &mut rng);
          let n = crs.size() as u64;
          let witnesses = (0..4).map(|_| Witness::rand(n, &mut rng)).collect::<Vec<_>>();
          (crs, witnesses)
      })) {

        let domain_separator = DomainSeparator::new("test-ipa-batch");
        let statements = witness.iter().map(|w| (w, w.statement(&crs))).collect::<Vec<_>>();
        // prover proves multiple statements
        let proofs = statements.iter().map(|(witness, statement)| {
            let domain_separator = BulletproofDomainSeparator::<Projective>::bulletproof_statement(domain_separator.clone()).ratchet();
            let domain_separator = BulletproofDomainSeparator::<Projective>::add_bulletproof(domain_separator, crs.size());
            let mut prover_state = domain_separator.to_prover_state();
            prover_state.public_points(&[statement.p])?;
            prover_state.ratchet().unwrap();
            let proof = prove(&mut prover_state, &crs, *statement, witness)?;
            Ok((statement, proof, domain_separator))
        }).collect::<Result<Vec<_>, ProofError>>()?;

        let verifications: Vec<ProverMSM<Projective>> = proofs.iter().map(|(statement, proof, domain_separator)| {
            let mut verifier_state = domain_separator.to_verifier_state(proof);
            verifier_state.public_points(&[statement.p])?;
            verifier_state.ratchet().unwrap();
            verify_aux(&mut verifier_state, &crs, statement)
        }).collect::<Result<Vec<_>, ProofError>>()?;

        let verifications = NonEmpty::from_vec(verifications).expect("non-empty vec");

        verify_batch_aux(verifications, &mut OsRng).expect("should verify batch");
      }




    }
}
