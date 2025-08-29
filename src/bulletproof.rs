use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_std::log2;
use spongefish::{
    DomainSeparator, ProofError, ProofResult, ProverState, VerifierState,
    codecs::arkworks_algebra::{
        FieldDomainSeparator, FieldToUnitDeserialize, FieldToUnitSerialize, GroupDomainSeparator,
        GroupToUnitDeserialize, GroupToUnitSerialize, UnitToField,
    },
};
use std::ops::Mul;
use tracing::{debug, instrument};

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
    prover_state: &mut ProverState,
    crs: &CRS<G>,
    statement: Statement<G>,
    witness: Witness<G::ScalarField>,
) -> ProofResult<Vec<u8>> {
    if witness.a.0.len() == 1 {
        debug!("Base case reached, adding final scalars");
        prover_state.add_scalars(&[witness.a.0[0], witness.b.0[0]])?;
        return Ok(prover_state.narg_string().to_vec());
    }

    let n = crs.size() / 2;
    debug!("Folding round with size {}", n * 2);
    let (g_left, g_right) = crs.g.split_at(n);
    let (h_left, h_right) = crs.h.split_at(n);
    let (a_left, a_right) = witness.a.0.split_at(n);
    let (b_left, b_right) = witness.b.0.split_at(n);

    let left = tracing::debug_span!("compute_left_commitment").in_scope(|| {
        let c_left = dot(a_left, b_right);
        crs.u.mul(c_left) + G::msm_unchecked(g_right, a_left) + G::msm_unchecked(h_left, b_right)
    });

    let right = tracing::debug_span!("compute_right_commitment").in_scope(|| {
        let c_right = dot(a_right, b_left);
        crs.u.mul(c_right) + G::msm_unchecked(g_left, a_right) + G::msm_unchecked(h_right, b_left)
    });

    prover_state.add_points(&[left, right])?;

    let [alpha]: [G::ScalarField; 1] = prover_state.challenge_scalars()?;
    let alpha_inv = alpha.inverse().expect("non-zero alpha");

    let crs = tracing::debug_span!("fold_crs").in_scope(|| {
        let g = fold_generators::<G>(g_left, g_right, alpha_inv, alpha);
        let h = fold_generators::<G>(h_left, h_right, alpha, alpha_inv);
        let u = crs.u;
        CRS { g, h, u }
    });

    let witness = tracing::debug_span!("fold_witness_vectors").in_scope(|| {
        let a = fold_scalars(a_left, a_right, alpha, alpha_inv);
        let b = fold_scalars(b_left, b_right, alpha_inv, alpha);
        Witness::new(Vector(a), Vector(b))
    });
    let statement = Statement {
        p: statement.p + left * alpha.square() + right * alpha_inv.square(),
    };
    prove(prover_state, &crs, statement, witness)
}

#[instrument(skip_all, fields(crs_size = crs.size()))]
pub fn verify<G: CurveGroup>(
    mut verifier_state: VerifierState,
    mut crs: CRS<G>,
    mut statement: Statement<G>,
) -> ProofResult<()> {
    let mut n = crs.size();

    while n != 1 {
        let [left, right]: [G; 2] = verifier_state.next_points()?;
        n /= 2;
        debug!("Verification round with size {}", n);
        let [alpha]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
        let alpha_inv = alpha.inverse().expect("non-zero alpha");
        tracing::debug_span!("fold_crs").in_scope(|| {
            let (g_left, g_right) = crs.g.split_at(n);
            let (h_left, h_right) = crs.h.split_at(n);
            crs.g = fold_generators::<G>(g_left, g_right, alpha_inv, alpha);
            crs.h = fold_generators::<G>(h_left, h_right, alpha, alpha_inv);
        });
        statement.p += left * alpha.square() + right * alpha_inv.square();
    }

    let [a, b]: [G::ScalarField; 2] = verifier_state.next_scalars()?;

    let c = a * b;
    debug!("Verification final scalars obtained");
    if (crs.g[0] * a + crs.h[0] * b + crs.u * c - statement.p).is_zero() {
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
    use tracing_subscriber::{EnvFilter, fmt::format::FmtSpan, fmt::time::UtcTime};

    #[ctor::ctor]
    fn init_console_subscriber() {
        let timer = UtcTime::rfc_3339();
        tracing_subscriber::fmt()
            .with_env_filter(EnvFilter::from_default_env())
            .with_span_events(FmtSpan::CLOSE)
            .with_timer(timer)
            .with_target(true)
            .with_thread_ids(false)
            .with_line_number(false)
            .with_file(false)
            .with_level(true)
            .with_ansi(true)
            .with_writer(std::io::stdout)
            .init();
    }

    proptest! {
      #![proptest_config(Config::with_cases(2))]
      #[test]
      fn proof_works((crs, inputs) in any::<CrsSize>().prop_map(|crs_size| {
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

          let proof = prove(&mut prover_state, &crs, statement.clone(), inputs).expect("proof should be generated");

          let mut verifier_state = domain_separator.to_verifier_state(&proof);
          verifier_state.public_points(&[statement.p]).expect("cannot add statment");
          verifier_state.ratchet().expect("failed to wratchet");
          verify(verifier_state, crs, statement).expect("proof should verify")

      }
    }
}
