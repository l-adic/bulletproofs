use ark_ec::CurveGroup;
use ark_ff::{BigInteger, Field, PrimeField};
use rayon::prelude::*;
use std::ops::Mul;
use tracing::instrument;

#[instrument(skip_all, fields(size = left.len()))]
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

#[instrument(skip_all, fields(size = left.len()))]
pub fn fold_scalars<Fr: Field>(left: &[Fr], right: &[Fr], x: Fr, y: Fr) -> Vec<Fr> {
    left.par_iter()
        .zip(right)
        .map(|(l, r)| *l * x + *r * y)
        .collect::<Vec<_>>()
}

#[instrument(skip_all, fields(size = xs.len()))]
pub fn dot<Fr: Field>(xs: &[Fr], ys: &[Fr]) -> Fr {
    xs.iter()
        .zip(ys)
        .fold(Fr::zero(), |acc, (x, y)| acc + (*x * *y))
}

// Decompose a field element into a vector of its bits (as field elements)
// E.g. for a field element a, return [a_0, a_1, ..., a_{n-1}] where
// a = a_0 * 2^0 + a_1 * 2^1 + ... + a_{n-1} * 2^{n-1}
pub fn bit_decomposition<Fr: PrimeField>(a: Fr) -> Vec<Fr> {
    let mut bits = Vec::with_capacity(Fr::MODULUS_BIT_SIZE as usize);
    let mut value = a.into_bigint();
    for _ in 0..Fr::MODULUS_BIT_SIZE {
        bits.push(if value.is_odd() {
            Fr::one()
        } else {
            Fr::zero()
        });
        value.div2();
    }
    bits
}

#[cfg(test)]
mod tests_range {
    use super::*;
    use ark_ec::AdditiveGroup;
    use ark_secp256k1::Fr;
    use ark_std::{One, UniformRand, Zero};
    use proptest::prelude::*;

    proptest! {
      #[test]
      fn test_bit_decomposition( x in prop::strategy::Just(Fr::rand(&mut ark_std::rand::thread_rng())))
        {
            let bits = bit_decomposition(x);
            let mut power_of_2 = Fr::one();
            let reconstructed = bits.iter().fold(Fr::zero(), |acc, b| {
                let result = acc + (*b * power_of_2);
                power_of_2 = power_of_2.double();
                result
            });
            prop_assert_eq!(x, reconstructed);
      }
    }
}
