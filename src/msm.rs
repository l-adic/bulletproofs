use std::{collections::HashMap, iter::successors};
use ark_ff::{One, UniformRand};
use ark_ec::CurveGroup;
use nonempty::NonEmpty;
use spongefish::{ProofError, ProofResult};
use tracing::instrument;

pub struct Msm<G: CurveGroup> {
    pub msm: HashMap<G::Affine, G::ScalarField>,
}


#[allow(clippy::new_without_default)]
impl<G: CurveGroup> Msm<G> {
    pub fn new() -> Self {
        Msm {
            msm: HashMap::new(),
        }
    }

    pub fn upsert(&mut self, base: G::Affine, scalar: G::ScalarField) {
        self.msm
            .entry(base)
            .and_modify(|s| *s += scalar)
            .or_insert(scalar);
    }

    pub fn upsert_batch(&mut self, bases: &[G::Affine], scalars: &[G::ScalarField]) {
        assert_eq!(bases.len(), scalars.len());
        for (base, scalar) in bases.iter().zip(scalars.iter()) {
            self.upsert(*base, *scalar);
        }
    }

    pub(crate) fn scale(&mut self, scalar: G::ScalarField) {
        for value in self.msm.values_mut() {
            *value *= scalar;
        }
    }

    pub(crate) fn batch(&mut self, rhs: Msm<G>) {

        for (base, scalar) in rhs.msm {
            self.upsert(base, scalar);
        }
    }

    pub(crate) fn bases_and_scalars(self) -> (Vec<G::Affine>, Vec<G::ScalarField>) {
        let (bases, scalars): (Vec<_>, Vec<_>) = self.msm.into_iter().unzip();
        (bases, scalars)
    }

    pub(crate) fn execute(self) -> G {
        let (bases, scalars) = self.bases_and_scalars();
        G::msm_unchecked(&bases, &scalars)
    }
}

#[instrument(skip_all, fields(n_proofs = proofs.len()), level = "debug")]
pub fn verify_batch_aux<G: CurveGroup, Rng: rand::Rng>(
    proofs: NonEmpty<Msm<G>>,
    rng: &mut Rng,
) -> ProofResult<()> {
    let alpha = G::ScalarField::rand(rng);
    let powers_of_alpha = successors(Some(G::ScalarField::one()), |state| Some(*state * alpha));
    let combined_msm = proofs
        .into_iter()
        .zip(powers_of_alpha)
        .map(|(mut proof, scalar)| {
            proof.scale(scalar);
            proof
        })
        .reduce(|mut acc, proof| {
            acc.batch(proof);
            acc
        })
        .expect("non-empty vec");
    let g = combined_msm.execute();
    if g.is_zero() {
        Ok(())
    } else {
        Err(ProofError::InvalidProof)
    }
}
