use ark_ec::CurveGroup;
use ark_ff::{One, UniformRand};
use nonempty::NonEmpty;
use spongefish::{ProofError, ProofResult};
use std::{collections::HashMap, iter::successors};
use tracing::instrument;

pub struct Msm<G: CurveGroup> {
    pub msm: HashMap<G::Affine, G::ScalarField>,
}

impl<G> FromIterator<(G::Affine, G::ScalarField)> for Msm<G>
where
    G: CurveGroup,
{
    fn from_iter<T: IntoIterator<Item = (G::Affine, G::ScalarField)>>(iter: T) -> Self {
        let mut msm = Msm::new();
        for (base, scalar) in iter {
            msm.upsert(base, scalar);
        }
        msm
    }
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

    // accepts any iterator of tuples of (base, scalar)
    pub fn upsert_batch<I>(&mut self, elems: I)
    where
        I: Iterator<Item = (G::Affine, G::ScalarField)>,
    {
        for (base, scalar) in elems {
            self.upsert(base, scalar);
        }
    }

    pub(crate) fn scale(&mut self, scalar: G::ScalarField) {
        for value in self.msm.values_mut() {
            *value *= scalar;
        }
    }

    pub(crate) fn scale_elem(&mut self, value: G::Affine, scalar: G::ScalarField) {
        if let Some(scalar_entry) = self.msm.get_mut(&value) {
            *scalar_entry *= scalar;
        }
    }

    pub(crate) fn scale_elems<I>(&mut self, elems: I)
    where
        I: Iterator<Item = (G::Affine, G::ScalarField)>,
    {
        for (base, factor) in elems {
            if let Some(scalar) = self.msm.get_mut(&base) {
                *scalar *= factor;
            }
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
