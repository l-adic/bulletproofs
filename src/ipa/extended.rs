use ark_ec::CurveGroup;
use ark_ff::Field;
use spongefish::{
    DomainSeparator, ProofError, ProofResult, ProverState, VerifierState,
    codecs::arkworks_algebra::{FieldDomainSeparator, GroupDomainSeparator, UnitToField},
};
use std::ops::Mul;

use crate::{
    ipa::{
        self as ipa, BulletproofDomainSeparator,
        types::{self as ipa_types, CRS, Statement, Witness},
    },
    msm::Msm,
};

pub trait ExtendedBulletproofDomainSeparator<G: CurveGroup> {
    fn extended_bulletproof_statement(self) -> Self;
    fn add_extended_bulletproof(self, len: usize) -> Self;
}

impl<G> ExtendedBulletproofDomainSeparator<G> for DomainSeparator
where
    G: CurveGroup,
    Self: GroupDomainSeparator<G> + FieldDomainSeparator<G::ScalarField>,
{
    fn extended_bulletproof_statement(self) -> Self {
        self.bulletproof_statement().add_scalars(1, "dot-product")
    }

    fn add_extended_bulletproof(self, len: usize) -> Self {
        self.challenge_scalars(1, "x").add_bulletproof(len)
    }
}

pub fn prove<G: CurveGroup>(
    prover_state: &mut ProverState,
    crs: &CRS<G>,
    ext_statement: &ipa_types::extended::Statement<G>,
    witness: &Witness<G>,
) -> ProofResult<Vec<u8>> {
    let [x]: [G::ScalarField; 1] = prover_state.challenge_scalars()?;
    let statement = Statement {
        p: ext_statement.p + crs.u.mul(x * ext_statement.c),
        witness_size: witness.size(),
    };
    let crs_mod = CRS {
        gs: crs.gs.clone(),
        hs: crs.hs.clone(),
        u: crs.u.mul(x).into_affine(),
    };
    ipa::prove(prover_state, &crs_mod, statement, witness)
}

pub fn verify<G: CurveGroup>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    ext_statement: &ipa_types::extended::Statement<G>,
) -> ProofResult<()>
where
    G::ScalarField: Field,
{
    let msm = verify_aux(verifier_state, crs, ext_statement)?;
    let g = msm.execute();
    if g.is_zero() {
        Ok(())
    } else {
        Err(ProofError::InvalidProof)
    }
}

pub fn verify_aux<G: CurveGroup>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    ext_statement: &ipa_types::extended::Statement<G>,
) -> ProofResult<Msm<G>> {
    let [x]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
    let statement = Statement {
        p: ext_statement.p + crs.u.mul(x * ext_statement.c),
        witness_size: ext_statement.witness_size,
    };
    let crs_mod = CRS {
        gs: crs.gs.clone(),
        hs: crs.hs.clone(),
        u: crs.u.mul(x).into_affine(),
    };
    let mut msm = ipa::verify_aux(verifier_state, &crs_mod, &statement)?;
    msm.msm.entry(crs.u).and_modify(|s| *s *= x);
    Ok(msm)
}
