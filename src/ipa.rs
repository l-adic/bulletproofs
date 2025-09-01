use ark_ec::CurveGroup;
use ark_ff::{Field, One};
use ark_std::log2;
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
    types::{CRS, Statement, Vector, Witness},
    utils::{dot, fold_generators, fold_scalars},
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

#[instrument(skip_all, fields(witness_size = witness.a.0.len()))]
pub fn prove<G: CurveGroup>(
    mut prover_state: ProverState,
    crs: &CRS<G>,
    statement: &Statement<G>,
    witness: &Witness<G::ScalarField>,
) -> ProofResult<Vec<u8>> {
    let mut n = crs.size();
    let mut g = crs.g.clone();
    let mut h = crs.h.clone();
    let mut statement = statement.clone();
    let mut witness = witness.clone();

    while n != 1 {
        n /= 2;
        let (g_left, g_right) = g.split_at(n);
        let (h_left, h_right) = h.split_at(n);
        let (a_left, a_right) = witness.a.0.split_at(n);
        let (b_left, b_right) = witness.b.0.split_at(n);

        let left = {
            let c_left = dot(a_left, b_right);
            crs.u.mul(c_left)
                + G::msm_unchecked(g_right, a_left)
                + G::msm_unchecked(h_left, b_right)
        };

        let right = {
            let c_right = dot(a_right, b_left);
            crs.u.mul(c_right)
                + G::msm_unchecked(g_left, a_right)
                + G::msm_unchecked(h_right, b_left)
        };

        prover_state.add_points(&[left, right])?;

        let [alpha]: [G::ScalarField; 1] = prover_state.challenge_scalars()?;
        let alpha_inv = alpha.inverse().expect("non-zero alpha");

        g = fold_generators::<G>(g_left, g_right, alpha_inv, alpha);
        h = fold_generators::<G>(h_left, h_right, alpha, alpha_inv);

        witness.a = Vector(fold_scalars(a_left, a_right, alpha, alpha_inv));
        witness.b = Vector(fold_scalars(b_left, b_right, alpha_inv, alpha));

        statement.p += left * alpha.square() + right * alpha_inv.square();
    }

    prover_state.add_scalars(&[witness.a.0[0], witness.b.0[0]])?;
    Ok(prover_state.narg_string().to_vec())
}

#[instrument(skip_all, fields(crs_size = crs.size()))]
pub fn verify_naive<G: CurveGroup>(
    mut verifier_state: VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
) -> ProofResult<()> {
    let mut n = crs.size();
    let mut g = crs.g.clone();
    let mut h = crs.h.clone();
    let mut statement = statement.clone();

    while n != 1 {
        let [left, right]: [G; 2] = verifier_state.next_points()?;
        n /= 2;
        let [alpha]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
        let alpha_inv = alpha.inverse().expect("non-zero alpha");
        {
            let (g_left, g_right) = g.split_at(n);
            let (h_left, h_right) = h.split_at(n);
            g = fold_generators::<G>(g_left, g_right, alpha_inv, alpha);
            h = fold_generators::<G>(h_left, h_right, alpha, alpha_inv);
        }
        statement.p += left * alpha.square() + right * alpha_inv.square();
    }

    let [a, b]: [G::ScalarField; 2] = verifier_state.next_scalars()?;
    let c = a * b;

    if (g[0] * a + h[0] * b + crs.u * c - statement.p).is_zero() {
        Ok(())
    } else {
        Err(ProofError::InvalidProof)
    }
}

#[instrument(skip_all, fields(crs_size = crs.size()))]
pub fn verify<G: CurveGroup>(
    mut verifier_state: VerifierState,
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
            let [alpha]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
            Ok(((left, right), alpha))
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
                            (transcript[log2_n - j - 1].1)
                                .inverse()
                                .expect("non-zero x")
                        }
                    })
                    .fold(G::ScalarField::one(), |acc, x| acc * x)
            })
            .collect::<Vec<_>>();

        let ss_inverse = ss
            .iter()
            .map(|x| x.inverse().expect("non-zero x"))
            .collect::<Vec<_>>();

        G::msm_unchecked(&crs.g, &ss).mul(a)
            + G::msm_unchecked(&crs.h, &ss_inverse).mul(b)
            + crs.u.mul(a * b)
    };

    let rhs = {
        transcript
            .into_iter()
            .fold(statement.p, |acc, ((left, right), x)| {
                acc + left * x.square() + right * x.inverse().expect("non-zero x").square()
            })
    };

    if (lhs - rhs).is_zero() {
        Ok(())
    } else {
        Err(ProofError::InvalidProof)
    }
}

#[cfg(test)]
mod tests_proof {
    use crate::types::{CrsSize, statement};

    use super::*;
    use ark_secp256k1::{self, Projective};
    use proptest::{prelude::*, test_runner::Config};
    use spongefish::DomainSeparator;
    use spongefish::codecs::arkworks_algebra::CommonGroupToUnit;

    proptest! {
      #![proptest_config(Config::with_cases(2))]
      #[test]
      fn test_prove_verify_works((crs, inputs) in any::<CrsSize>().prop_map(|crs_size| {
          let crs: CRS<Projective> = CRS::rand(crs_size);
          let n = crs.size() as u64;
          let inputs = Witness::rand(n);
          (crs, inputs)
      })) {
          let domain_separator = DomainSeparator::new("example.com");
          // add the IO of the bulletproof statement
          let domain_separator =
              BulletproofDomainSeparator::<Projective>::bulletproof_statement(domain_separator).ratchet();
          // add the IO of the bulletproof protocol (the transcript)
          let domain_separator = BulletproofDomainSeparator::<Projective>::add_bulletproof(domain_separator, crs.size());
          let mut prover_state = domain_separator.to_prover_state();

          let statement = statement(&crs, &inputs);
          prover_state.public_points(&[statement.p]).unwrap();
          prover_state.ratchet().unwrap();

          let proof = prove(prover_state, &crs, &statement, &inputs).expect("proof should be generated");

          let mut verifier_state = domain_separator.to_verifier_state(&proof);
          verifier_state.public_points(&[statement.p]).expect("cannot add statment");
          verifier_state.ratchet().expect("failed to wratchet");
          verify_naive(verifier_state, &crs, &statement).expect("proof should verify");

          let mut fast_verifier_state = domain_separator.to_verifier_state(&proof);
          fast_verifier_state.public_points(&[statement.p]).expect("cannot add statment");
          fast_verifier_state.ratchet().expect("failed to wratchet");
          verify(fast_verifier_state, &crs, &statement).expect("proof should verify")

      }
    }
}
