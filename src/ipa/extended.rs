use ark_ec::{CurveGroup, PrimeGroup};
// use ark_ff::Field;
use spongefish::{
    Codec, Encoding, NargDeserialize, ProverState, VerificationError, VerificationResult,
    VerifierState,
};
use std::ops::Mul;

use crate::{
    ipa::{
        self as ipa,
        types::{self as ipa_types, CRS, Statement, Witness},
    },
    msm::Msm,
};

pub trait ExtendedBulletproofDomainSeparator<G: CurveGroup> {
    fn extended_bulletproof_statement(self) -> Self;
    fn add_extended_bulletproof(self, len: usize) -> Self;
}

//impl<G> ExtendedBulletproofDomainSeparator<G> for DomainSeparator
//where
//    G: CurveGroup,
//    Self: GroupDomainSeparator<G> + FieldDomainSeparator<G::ScalarField>,
//{
//    fn extended_bulletproof_statement(self) -> Self {
//        self.bulletproof_statement().add_scalars(1, "dot-product")
//    }
//
//    fn add_extended_bulletproof(self, len: usize) -> Self {
//        self.challenge_scalars(1, "x").add_bulletproof(len)
//    }
//}

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
) -> VerificationResult<()>
where
    G::ScalarField: Codec,
{
    let msm = verify_aux(verifier_state, crs, ext_statement)?;
    let g = msm.execute();
    if g.is_zero() {
        Ok(())
    } else {
        Err(VerificationError)
    }
}

pub fn verify_aux<G: CurveGroup + Encoding + NargDeserialize>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    ext_statement: &ipa_types::extended::Statement<G>,
) -> VerificationResult<Msm<G>>
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
