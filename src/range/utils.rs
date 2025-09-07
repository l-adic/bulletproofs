use ark_ec::CurveGroup;
use ark_ff::{BigInteger, Field, One, PrimeField};
use std::ops::Mul;

// Decompose a field element into a vector of its bits (as field elements)
// E.g. for a field element a, return [a_0, a_1, ..., a_{n-1}] where
// a = a_0 * 2^0 + a_1 * 2^1 + ... + a_{n-1} * 2^{n-1}
pub(super) fn bit_decomposition<Fr: PrimeField>(a: Fr) -> Vec<Fr> {
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

pub(super) fn power_sequence<F: Field>(base: F, n: usize) -> Vec<F> {
    let mut res = vec![F::one(); n];
    for i in 1..n {
        res[i] = res[i - 1] * base;
    }
    res
}

pub(super) fn create_hs_prime<G: CurveGroup>(
    hs: &[G::Affine],
    y: G::ScalarField,
) -> Vec<G::Affine> {
    let y_inv = y.inverse().expect("non-zero y");
    let ys_inv = std::iter::successors(Some(G::ScalarField::one()), |&x| (Some(x * y_inv)));
    G::normalize_batch(
        &hs.iter()
            .zip(ys_inv)
            .map(|(h, y_inv)| h.mul(y_inv))
            .collect::<Vec<_>>(),
    )
}

#[cfg(test)]
mod tests {

    use super::*;
    use ark_ec::AdditiveGroup;
    use ark_secp256k1::Fr;
    use ark_std::{One, UniformRand, Zero};
    use proptest::prelude::*;
    use rand::rngs::OsRng;

    proptest! {
      #[test]
      fn test_bit_decomposition( x in prop::strategy::Just(Fr::rand(&mut OsRng)))
        {
            let bits = bit_decomposition(x);
            // assert all bits are either 0 or 1
            for b in &bits {
                prop_assert!(*b == Fr::zero() || *b == Fr::one());
            }
            // assert that the length is the modulus bit size
            prop_assert_eq!(bits.len(), Fr::MODULUS_BIT_SIZE as usize);

            // assrt that reconstructing the field element from its bits gives the original element
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
