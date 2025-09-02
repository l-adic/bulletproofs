use crate::ipa::utils::dot;
use ark_ff::{BigInteger, Field, PrimeField};

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

pub struct VectorPolynomial<const N: usize, Fr: Field> {
    pub coeffs: Vec<[Fr; N]>,
}

// The inner product is defined for l, r \elem F^{n}[X] (of the same degreee d) as
// <l,r> = \sum_{i=0}^{d} \sum_{j=0}^{i}} <l_i, r_j> X^{i+j}
impl<Fr: Field, const N: usize> VectorPolynomial<N, Fr> {
    pub fn inner_product(&self, rhs: &Self) -> Vec<Fr> {
        assert!(
            self.coeffs.len() == rhs.coeffs.len(),
            "Vector polynomials must have the same degree"
        );
        let d = self.coeffs.len() - 1;
        let mut result_coeffs = vec![Fr::zero(); 2 * d];

        for i in 0..=d {
            for j in 0..=i {
                let dot_product = dot(&self.coeffs[i], &rhs.coeffs[j]);
                result_coeffs[i + j] += dot_product;
            }
        }
        result_coeffs
    }

    pub fn evaluate(&self, x: Fr) -> [Fr; N] {
        let mut result = [Fr::zero(); N];
        let mut power_of_x = Fr::one();
        for coeff in &self.coeffs {
            for i in 0..N {
                result[i] += coeff[i] * power_of_x;
            }
            power_of_x *= x;
        }
        result
    }
}
