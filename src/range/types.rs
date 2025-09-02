use ark_ec::CurveGroup;
use ark_ff::{BigInteger, PrimeField};
use std::ops::Mul;

pub struct CRS<G: CurveGroup> {
    pub gs: Vec<G::Affine>,
    pub hs: Vec<G::Affine>,
    pub g: G::Affine,
    pub h: G::Affine,
}

impl<G: CurveGroup> CRS<G> {
    pub fn size(&self) -> usize {
        self.gs.len()
    }
}

pub struct Witness<const N: usize, Fr> {
    pub v: Fr,
    pub gamma: Fr,
}

impl<Fr: PrimeField, const N: usize> Witness<N, Fr> {
    pub fn new<Rng: rand::Rng>(v: Fr, rng: &mut Rng) -> Self {
        assert!(v.into_bigint().num_bits() as usize <= N);
        Witness {
            v,
            gamma: Fr::rand(rng),
        }
    }
}

#[derive(Debug)]
pub struct Statement<const N: usize, G> {
    pub v: G,
}

impl<G: CurveGroup, const N: usize> Statement<N, G> {
    pub fn new(crs: &CRS<G>, witness: &Witness<N, G::ScalarField>) -> Self {
        Statement {
            v: crs.g.mul(witness.v) + crs.h.mul(witness.gamma),
        }
    }
}
