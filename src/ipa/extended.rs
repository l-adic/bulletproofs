use ark_ec::{CurveGroup, PrimeGroup};
// use ark_ff::Field;
use crate::BulletproofResult;
use spongefish::{Codec, Encoding, NargDeserialize, ProverState, VerifierState};
use std::ops::Mul;

use crate::{
    ipa::{
        self as ipa,
        types::{self as ipa_types, CRS, Statement, Witness},
    },
    msm::Msm,
};

pub fn prove<G: CurveGroup + Encoding>(
    prover_state: &mut ProverState,
    crs: &CRS<G>,
    ext_statement: &ipa_types::extended::Statement<G>,
    witness: &Witness<G>,
) -> Vec<u8>
where
    <G as PrimeGroup>::ScalarField: Codec,
{
    let x: G::ScalarField = prover_state.verifier_message();
    let statement = Statement {
        p: ext_statement.p + crs.u.mul(x * ext_statement.c),
        witness_size: witness.size() as u64,
    };
    let crs_mod = CRS {
        gs: crs.gs.clone(),
        hs: crs.hs.clone(),
        u: crs.u.mul(x).into_affine(),
    };
    ipa::prove(prover_state, &crs_mod, statement, witness)
}

pub fn verify<G: CurveGroup + Encoding + NargDeserialize>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    ext_statement: &ipa_types::extended::Statement<G>,
) -> BulletproofResult<()>
where
    G::ScalarField: Codec,
{
    let msm = verify_aux(verifier_state, crs, ext_statement)?;
    let g = msm.execute();
    if g.is_zero() {
        Ok(())
    } else {
        Err(crate::VerificationError)
    }
}

pub fn verify_aux<G: CurveGroup + Encoding + NargDeserialize>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    ext_statement: &ipa_types::extended::Statement<G>,
) -> BulletproofResult<Msm<G>>
where
    G::ScalarField: Codec,
{
    let x: G::ScalarField = verifier_state.verifier_message();
    let statement = Statement {
        p: ext_statement.p + crs.u.mul(x * ext_statement.c),
        witness_size: ext_statement.witness_size,
    };
    let mut msm = ipa::verify_aux(verifier_state, crs, &statement)?;
    msm.scale_elem(crs.u, x);
    Ok(msm)
}
