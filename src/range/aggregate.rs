use crate::range::types::CRS;
use ark_ec::CurveGroup;
use ark_ff::{BigInteger, PrimeField};
use std::array;
use std::ops::Mul;

pub struct Witness<const N: usize, const M: usize, Fr> {
    pub v: [Fr; M],
    pub gamma: [Fr; M],
}

impl<const N: usize, const M: usize, Fr: PrimeField> Witness<N, M, Fr> {
    pub fn new<Rng: rand::Rng>(v: [Fr; M], rang: &mut Rng) -> Self
    where
        Fr: PrimeField,
    {
        for &val in &v {
            assert!(val.into_bigint().num_bits() as usize <= N);
        }
        Witness {
            v,
            gamma: array::from_fn(|_| Fr::rand(rang)),
        }
    }
}

pub struct Statement<const N: usize, const M: usize, G> {
    pub v: [G; M],
}

impl<const N: usize, const M: usize, G: CurveGroup> Statement<N, M, G> {
    pub fn new(crs: &CRS<G>, witness: Witness<N, M, G::ScalarField>) -> Self {
        let v = array::from_fn(|i| crs.g.mul(witness.v[i]) + crs.h.mul(witness.gamma[i]));
        Statement { v }
    }
}
