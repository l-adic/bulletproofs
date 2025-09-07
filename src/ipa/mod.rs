pub mod extended;
pub mod types;

use ark_ec::CurveGroup;
use ark_ff::{Field, One, batch_inversion};
use ark_std::log2;
use rayon::prelude::*;
use spongefish::{
    DomainSeparator, ProofError, ProofResult, ProverState, VerifierState,
    codecs::arkworks_algebra::{
        FieldDomainSeparator, FieldToUnitDeserialize, FieldToUnitSerialize, GroupDomainSeparator,
        GroupToUnitDeserialize, GroupToUnitSerialize, UnitToField,
    },
};
use std::ops::Mul;
use tracing::instrument;

use crate::{
    ipa::types::{CRS, Statement, Witness},
    vector_ops::inner_product,
};

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
    statement: &Statement<G>,
    witness: &Witness<G>,
) -> ProofResult<Vec<u8>> {
    let mut n = crs.size();
    let mut gs = crs.gs.clone();
    let mut hs = crs.hs.clone();
    let mut statement = statement.clone();
    let mut witness = witness.clone();

    while n != 1 {
        n /= 2;
        let (g_left, g_right) = gs.split_at(n);
        let (h_left, h_right) = hs.split_at(n);
        let (a_left, a_right) = witness.a.split_at(n);
        let (b_left, b_right) = witness.b.split_at(n);

        let left = {
            //let c_left = //slice_ops::dot(a_left, b_right);
            let c_left = inner_product(a_left.iter().copied(), b_right.iter().copied()); //inner_product(a_left, b_right);
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

#[instrument(skip_all, fields(crs_size = crs.size()), level = "debug")]
pub fn verify<G: CurveGroup>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
) -> ProofResult<()>
where
    G::ScalarField: Field,
{
    let n = crs.size();
    let log2_n = log2(n) as usize;

    let transcript: Vec<((G, G), G::ScalarField)> = (0..log2_n)
        .map(|_| {
            let [left, right]: [G; 2] = verifier_state.next_points()?;
            let [x]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
            Ok(((left, right), x))
        })
        .collect::<ProofResult<Vec<_>>>()?;

    let lhs: G = {
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

        crs.u.mul(a * b) + {
            let bases: Vec<G::Affine> = crs
                .gs
                .iter()
                .copied()
                .chain(crs.hs.iter().copied())
                .collect();
            let scalars: Vec<G::ScalarField> = ss
                .iter()
                .map(|s| *s * a)
                .chain(ss_inverse.iter().map(|s_inv| *s_inv * b))
                .collect();
            G::msm_unchecked(&bases, &scalars)
        }
    };

    let rhs = {
        transcript
            .into_iter()
            .fold(statement.p, |acc, ((left, right), x)| {
                acc + left * x.square() + right * x.inverse().expect("non-zero inverse").square()
            })
    };

    if (lhs - rhs).is_zero() {
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

            let proof = prove(&mut prover_state, &crs, &statement, &witness).expect("proof should be generated");

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
}
