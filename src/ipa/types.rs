use ark_ec::CurveGroup;
use ark_ff::UniformRand;
use proptest::prelude::*;
use rand::rngs::OsRng;
use std::ops::{Add, Mul};

use crate::vector_ops::{VectorOps, inner_product};

#[derive(Clone, Debug)]
pub struct CRS<G: CurveGroup> {
    pub gs: Vec<G::Affine>,
    pub hs: Vec<G::Affine>,
    pub u: G::Affine,
}

#[derive(Clone, Copy, Debug)]
pub struct CrsSize {
    pub log2_size: u64,
}

impl Arbitrary for CrsSize {
    type Parameters = ();
    type Strategy = proptest::strategy::BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        (2..=16u8)
            .prop_map(|log2_size| CrsSize {
                log2_size: log2_size as u64,
            })
            .boxed()
    }
}

impl<G: CurveGroup> CRS<G> {
    pub fn rand<Rng: rand::Rng>(size: CrsSize, rng: &mut Rng) -> Self {
        let size = 1 << size.log2_size;
        let gs = (0..size).map(|_| G::Affine::rand(rng)).collect();
        let hs = (0..size).map(|_| G::Affine::rand(&mut OsRng)).collect();
        let u = G::Affine::rand(&mut OsRng);
        CRS { gs, hs, u }
    }

    pub fn size(&self) -> usize {
        self.gs.len()
    }
}

#[derive(Clone, Debug)]
pub struct Witness<G: CurveGroup> {
    pub a: Vec<G::ScalarField>,
    pub b: Vec<G::ScalarField>,
    c: G::ScalarField,
}

impl<G: CurveGroup> Witness<G> {
    pub fn new(a: Vec<G::ScalarField>, b: Vec<G::ScalarField>) -> Self {
        let c = inner_product(a.iter().copied(), b.iter().copied());
        Witness { a, b, c }
    }

    pub fn rand<Rng: rand::Rng>(size: u64, rng: &mut Rng) -> Self {
        let a = (0..size)
            .map(|_| G::ScalarField::rand(rng))
            .collect::<Vec<_>>();
        let b = (0..size)
            .map(|_| G::ScalarField::rand(rng))
            .collect::<Vec<_>>();
        let c = inner_product(a.iter().copied(), b.iter().copied());
        Witness { a, b, c }
    }

    pub fn c(&self) -> G::ScalarField {
        self.c
    }

    pub fn statement(&self, crs: &CRS<G>) -> Statement<G> {
        let g: G = G::msm_unchecked(&crs.gs, &self.a);
        let h: G = G::msm_unchecked(&crs.hs, &self.b);
        let p: G = g.add(&h).add(&crs.u.mul(self.c));
        Statement { p }
    }

    pub fn extended_statement(&self, crs: &CRS<G>) -> extended::Statement<G> {
        let bases: Vec<G::Affine> = crs
            .gs
            .iter()
            .copied()
            .chain(crs.hs.iter().copied())
            .collect();
        let scalars: Vec<G::ScalarField> = self
            .a
            .iter()
            .copied()
            .chain(self.b.iter().copied())
            .collect();
        let p = G::msm_unchecked(&bases, &scalars);
        extended::Statement { p, c: self.c() }
    }
}

impl<G: CurveGroup> Add for Witness<G> {
    type Output = Witness<G>;

    fn add(self, rhs: Self) -> Self::Output {
        assert_eq!(self.a.len(), rhs.a.len());
        assert_eq!(self.b.len(), rhs.b.len());
        let a = self
            .a
            .iter()
            .copied()
            .vector_add(rhs.a.iter().copied())
            .collect();
        let b = self
            .b
            .iter()
            .copied()
            .vector_add(rhs.b.iter().copied())
            .collect();
        Witness {
            a,
            b,
            c: self.c + rhs.c,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Statement<G: CurveGroup> {
    pub p: G,
}

impl<G: CurveGroup> Add for Statement<G> {
    type Output = Statement<G>;

    fn add(self, rhs: Self) -> Self::Output {
        Statement { p: self.p + rhs.p }
    }
}

pub mod extended {
    use ark_ec::CurveGroup;

    pub struct Statement<G: CurveGroup> {
        pub p: G,
        pub c: G::ScalarField,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_secp256k1::{self, Projective};
    use proptest::test_runner::Config;

    proptest! {
      #![proptest_config(Config::with_cases(2))]
      #[test]
      fn statements_are_additive((crs, witness1, witness2) in any::<CrsSize>().prop_map(|crs_size| {
          let mut rng = OsRng;
          let crs: CRS<Projective> = CRS::rand(crs_size, &mut rng);
          let n = crs.size() as u64;
          let witness1 = Witness::rand(n, &mut rng);
          let witness2 = Witness::rand(n, &mut rng);
          (crs, witness1, witness2)
      })) {
          let c1 = witness1.statement(&crs);
          let c2 = witness2.statement(&crs);
          let c =  (witness1 + witness2).statement(&crs);
          prop_assert!(c.p == c1.p + c2.p);
      }
    }
}
