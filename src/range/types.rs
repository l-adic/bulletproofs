use ark_ec::CurveGroup;
use ark_ff::{BigInteger, Field, PrimeField};
use ark_std::log2;
use std::ops::Mul;

use crate::ipa::types::CrsSize;
use crate::{
    ipa::{self},
    vector_ops::inner_product,
};

pub struct CRS<G: CurveGroup> {
    pub ipa_crs: ipa::types::CRS<G>,
    pub g: G::Affine,
    pub h: G::Affine,
}

impl<G: CurveGroup> CRS<G> {
    pub fn rand<Rng: rand::Rng>(n: usize, rng: &mut Rng) -> Self
where {
        let ipa_crs = {
            let log2_size = log2(n) as u64;
            ipa::types::CRS::rand(CrsSize { log2_size }, rng)
        };
        let g = G::rand(rng).into_affine();
        let h = G::rand(rng).into_affine();
        CRS { ipa_crs, g, h }
    }

    pub fn size(&self) -> usize {
        self.ipa_crs.size()
    }
}

pub struct Witness<Fr> {
    pub v: Fr,
    pub gamma: Fr,
    pub n_bits: usize,
}

impl<Fr: PrimeField> Witness<Fr> {
    pub fn new<Rng: rand::Rng>(v: Fr, n_bits: usize, rng: &mut Rng) -> Self {
        assert!(
            v.into_bigint().num_bits() as usize <= n_bits,
            "Value exceeds n_bits limit"
        );
        Witness {
            v,
            gamma: Fr::rand(rng),
            n_bits,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Statement<G> {
    pub v: G,
    pub n_bits: usize,
}

impl<G: CurveGroup> Statement<G> {
    pub fn new(crs: &CRS<G>, witness: &Witness<G::ScalarField>) -> Self {
        Statement {
            v: crs.g.mul(witness.v) + crs.h.mul(witness.gamma),
            n_bits: witness.n_bits,
        }
    }
}

pub(crate) struct VectorPolynomial<Fr: Field> {
    pub coeffs: Vec<Vec<Fr>>,
    n: usize,
}

impl<Fr: Field> VectorPolynomial<Fr> {
    pub(crate) fn new(coeffs: Vec<Vec<Fr>>, n: usize) -> Self {
        assert!(!coeffs.is_empty(), "Coefficient vector cannot be empty");
        assert!(n > 0, "Coefficient vectors cannot be empty");
        for coeff in &coeffs {
            assert_eq!(coeff.len(), n, "All coefficient vectors must have length n");
        }
        Self { coeffs, n }
    }

    #[cfg(test)]
    pub(crate) fn rand<Rng: rand::Rng>(degree: usize, n: usize, rng: &mut Rng) -> Self
    where
        Fr: PrimeField,
    {
        let mut coeffs = Vec::with_capacity(degree + 1);
        for _ in 0..=degree {
            coeffs.push((0..n).map(|_| Fr::rand(rng)).collect());
        }
        Self::new(coeffs, n)
    }

    pub(crate) fn inner_product(&self, rhs: &Self) -> Vec<Fr> {
        assert!(
            self.coeffs.len() == rhs.coeffs.len(),
            "Vector polynomials must have the same degree"
        );
        assert_eq!(self.n, rhs.n, "Vector polynomials must have the same n");
        let degree = self.coeffs.len() - 1;
        let mut result_coeffs = vec![Fr::zero(); (2 * degree) + 1];

        for i in 0..=degree {
            for j in 0..=degree {
                let dot_product = inner_product(
                    self.coeffs[i].iter().copied(),
                    rhs.coeffs[j].iter().copied(),
                );
                result_coeffs[i + j] += dot_product;
            }
        }
        result_coeffs
    }

    pub(crate) fn evaluate(&self, x: Fr) -> Vec<Fr> {
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

pub mod aggregate {
    use crate::range::types::CRS;
    use ark_ec::CurveGroup;
    use ark_ff::{BigInteger, PrimeField};
    use std::ops::Mul;

    pub struct Witness<Fr> {
        pub v: Vec<Fr>,
        pub gamma: Vec<Fr>,
        pub n_bits: usize,
    }

    impl<Fr: PrimeField> Witness<Fr> {
        pub fn new<Rng: rand::Rng>(v: Vec<Fr>, n_bits: usize, rang: &mut Rng) -> Self {
            for val in &v {
                assert!(val.into_bigint().num_bits() as usize <= n_bits);
            }

            let gamma = (0..v.len()).map(|_| Fr::rand(rang)).collect();
            Witness { v, gamma, n_bits }
        }

        #[allow(clippy::len_without_is_empty)]
        pub fn len(&self) -> usize {
            self.v.len()
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub struct Statement<G> {
        pub v: Vec<G>,
        pub n_bits: usize,
    }

    impl<G: CurveGroup> Statement<G> {
        pub fn new(crs: &CRS<G>, witness: &Witness<G::ScalarField>) -> Self {
            Statement {
                v: (0..witness.len())
                    .map(|i| crs.g.mul(witness.v[i]) + crs.h.mul(witness.gamma[i]))
                    .collect(),
                n_bits: witness.n_bits,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_secp256k1::Fr;
    use ark_std::{UniformRand, Zero};
    use proptest::prelude::*;
    use rand::rngs::OsRng;

    // proptest that evaluating an inner product of two VectorPolynomials is the inner product of the evaluations
    proptest! {
      #[test]
      fn test_inner_product_eval(
        degree in 1usize..5,
        n in 1usize..5,
        x in prop::strategy::Just(Fr::rand(&mut OsRng))
      ) {
            let mut rng = OsRng;
            let poly1 = VectorPolynomial::<Fr>::rand(degree, n, &mut rng);
            let poly2 = VectorPolynomial::<Fr>::rand(degree, n, &mut rng);
            let t = VectorPolynomial::inner_product(&poly1, &poly2);
            let eval1 = poly1.evaluate(x);
            let eval2 = poly2.evaluate(x);
            let inner_prod_eval = inner_product(eval1.into_iter(), eval2.into_iter());
            let powers_of_x = (0..=degree*2).map(|i| x.pow([i as u64])).collect::<Vec<_>>();
            let eval_t_at_x = t.iter().zip(powers_of_x.iter()).fold(Fr::zero(), |acc, (coeff, power)| acc + (*coeff * *power));
            prop_assert_eq!(inner_prod_eval, eval_t_at_x);
      }
    }
}
