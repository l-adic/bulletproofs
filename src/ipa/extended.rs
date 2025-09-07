use ark_ec::CurveGroup;
use ark_ff::Field;
use spongefish::{
    DomainSeparator, ProofResult, ProverState, VerifierState,
    codecs::arkworks_algebra::{FieldDomainSeparator, GroupDomainSeparator, UnitToField},
};
use std::ops::Mul;

use crate::ipa::{
    self as ipa, BulletproofDomainSeparator,
    types::{self as ipa_types, CRS, Statement, Witness},
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
    /// The IO of the bulletproof statement
    fn extended_bulletproof_statement(self) -> Self {
        self.bulletproof_statement().add_scalars(1, "dot-product")
    }

    /// The IO of the bulletproof protocol
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
    };
    let crs_mod = CRS {
        gs: crs.gs.clone(),
        hs: crs.hs.clone(),
        u: crs.u.mul(x).into_affine(),
    };
    ipa::prove(prover_state, &crs_mod, &statement, witness)
}

pub fn verify<G: CurveGroup>(
    mut verifier_state: VerifierState,
    crs: &CRS<G>,
    ext_statement: &ipa_types::extended::Statement<G>,
) -> ProofResult<()>
where
    G::ScalarField: Field,
{
    let [x]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
    let statement = Statement {
        p: ext_statement.p + crs.u.mul(x * ext_statement.c),
    };
    let crs_mod = CRS {
        gs: crs.gs.clone(),
        hs: crs.hs.clone(),
        u: crs.u.mul(x).into_affine(),
    };
    ipa::verify(verifier_state, &crs_mod, &statement)
}
