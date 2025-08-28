use ark_ec::{CurveGroup, PrimeGroup, scalar_mul::variable_base::VariableBaseMSM};
use ark_ff::UniformRand;
use ark_secp256k1::{self, Affine, Fr, Projective};
use rand::rngs::OsRng;
use std::ops::{Add, Mul};

#[derive(Clone, Debug)]
pub struct Vector(Vec<Fr>);

impl Vector {
    pub fn rand(size: u64) -> Self {
        let vec = {
            let mut v = Vec::new();
            for _ in 0..size {
                v.push(UniformRand::rand(&mut OsRng));
            }
            Vector(v)
        };
        vec
    }
}

impl Add for Vector {
    type Output = Vector;

    fn add(self, rhs: Self) -> Self::Output {
        let mut result = Vec::new();
        for (a, b) in self.0.iter().zip(rhs.0.iter()) {
            result.push(*a + *b);
        }
        Vector(result)
    }
}

#[derive(Clone, Debug)]
pub struct SRS {
    pub g: Vec<Affine>,
    pub h: Affine,
}

#[derive(Clone, Copy)]
pub struct Commitment(pub Projective);

impl Add for Commitment {
    type Output = Commitment;

    fn add(self, rhs: Self) -> Self::Output {
        Commitment(self.0 + rhs.0)
    }
}

impl SRS {
    // Hash to curve to create an srs of the given size
    pub fn new(size: u64, salt: u64) -> Self {
        let mut g = Vec::new();
        let generator = ark_secp256k1::Projective::generator();
        for i in 0..size {
            let hash = ark_secp256k1::Fr::from(i + salt);
            let point = generator.mul(hash);
            g.push(point.into_affine());
        }
        let h = ark_secp256k1::Projective::generator()
            .mul(Fr::from(size))
            .into_affine();
        SRS { g, h }
    }

    pub fn commit(&self, scalars: &Vector, blinder: Fr) -> Commitment {
        let x: Projective = VariableBaseMSM::msm(&self.g, &scalars.0).unwrap();
        Commitment(x.add(self.h.mul(blinder)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::UniformRand;
    use proptest::{prelude::*, test_runner::Config};
    use rand::rngs::OsRng;

    proptest! {
      #![proptest_config(Config::with_cases(2))]
      #[test]
      fn commitments_are_additive((srs, v1,v2) in any::<(u16,u64)>().prop_map(|(size, salt)| {
          let size = size as u64;
          let srs = SRS::new(size, salt);
          (srs, Vector::rand(size), Vector::rand(size))
      })) {
          let blinder1 = Fr::rand(&mut OsRng);
          let blinder2 = Fr::rand(&mut OsRng);
          let c1 = srs.commit(&v1, blinder1);
          let c2 = srs.commit(&v2, blinder2);
          let c = srs.commit(&(v1 + v2), blinder1 + blinder2);
          prop_assert!(c.0 == c1.0 + c2.0);
      }
    }
}
