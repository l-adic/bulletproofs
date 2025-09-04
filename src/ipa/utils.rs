use ark_ec::CurveGroup;
use ark_ff::Field;
use rayon::prelude::*;
use std::ops::Mul;
use tracing::instrument;

#[instrument(skip_all, fields(size = left.len()), level = "debug")]
pub fn fold_generators<G: CurveGroup>(
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

pub fn fold_scalars<Fr: Field>(left: &[Fr], right: &[Fr], x: Fr, y: Fr) -> Vec<Fr> {
    left.par_iter()
        .zip(right)
        .map(|(l, r)| *l * x + *r * y)
        .collect::<Vec<_>>()
}

pub fn dot<Fr: Field>(xs: &[Fr], ys: &[Fr]) -> Fr {
    xs.iter()
        .zip(ys)
        .fold(Fr::zero(), |acc, (x, y)| acc + (*x * *y))
}

pub fn sum<Fr: Field>(xs: &[Fr]) -> Fr {
    xs.iter().fold(Fr::zero(), |acc, x| acc + *x)
}
