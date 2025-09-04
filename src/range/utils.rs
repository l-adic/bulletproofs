use crate::ipa::utils::dot;
use ark_ff::{BigInteger, Field, PrimeField};
use tracing::instrument;

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

pub struct VectorPolynomial<Fr: Field> {
    pub coeffs: Vec<Vec<Fr>>,
    pub n: usize,
}

impl<Fr: Field> VectorPolynomial<Fr> {
    pub fn new(coeffs: Vec<Vec<Fr>>, n: usize) -> Self {
        for coeff in &coeffs {
            assert_eq!(coeff.len(), n, "All coefficient vectors must have length n");
        }
        Self { coeffs, n }
    }

    #[cfg(test)]
    pub fn rand(degree: usize, n: usize) -> Self
    where
        Fr: PrimeField,
    {
        let mut coeffs = Vec::with_capacity(degree + 1);
        let mut rng = ark_std::rand::thread_rng();
        for _ in 0..=degree {
            coeffs.push((0..n).map(|_| Fr::rand(&mut rng)).collect());
        }
        Self { coeffs, n }
    }
}

// The inner product is defined for l, r \elem F^{n}[X] (of the same degreee d) as
// <l,r> = \sum_{i=0}^{d} \sum_{j=0}^{i}} <l_i, r_j> X^{i+j}
impl<Fr: Field> VectorPolynomial<Fr> {
    #[instrument(skip(self, rhs))]
    pub fn inner_product(&self, rhs: &Self) -> Vec<Fr> {
        assert!(
            self.coeffs.len() == rhs.coeffs.len(),
            "Vector polynomials must have the same degree"
        );
        assert_eq!(self.n, rhs.n, "Vector polynomials must have the same n");
        let degree = self.coeffs.len() - 1;
        let mut result_coeffs = vec![Fr::zero(); (2 * degree) + 1];

        for i in 0..=degree {
            for j in 0..=degree {
                let dot_product = dot(&self.coeffs[i], &rhs.coeffs[j]);
                result_coeffs[i + j] += dot_product;
            }
        }
        result_coeffs
    }

    pub fn evaluate(&self, x: Fr) -> Vec<Fr> {
        let mut result = vec![Fr::zero(); self.n];
        let mut power_of_x = Fr::one();
        for coeff in &self.coeffs {
            for i in 0..self.n {
                result[i] += coeff[i] * power_of_x;
            }
            power_of_x *= x;
        }
        result
    }
}

pub fn power_sequence<F: Field>(base: F, n: usize) -> Vec<F> {
    let mut res = vec![F::one(); n];
    for i in 1..n {
        res[i] = res[i - 1] * base;
    }
    res
}

#[cfg(test)]
mod tests {
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

    // proptest that evaluating an inner product of two VectorPolynomials is the inner product of the evaluations
    proptest! {
      #[test]
      fn test_inner_product_eval(
        degree in 1usize..5,
        x in prop::strategy::Just(Fr::rand(&mut ark_std::rand::thread_rng()))
      ) {
            let poly1 = VectorPolynomial::<Fr>::rand(degree, 4);
            let poly2 = VectorPolynomial::<Fr>::rand(degree, 4);
            let t = poly1.inner_product(&poly2);
            let eval1 = poly1.evaluate(x);
            let eval2 = poly2.evaluate(x);
            let inner_prod_eval = dot(&eval1, &eval2);
            let powers_of_x = (0..=degree*2).map(|i| x.pow([i as u64])).collect::<Vec<_>>();
            let eval_t_at_x = t.iter().zip(powers_of_x.iter()).fold(Fr::zero(), |acc, (coeff, power)| acc + (*coeff * *power));
            prop_assert_eq!(inner_prod_eval, eval_t_at_x);
      }
    }
}
