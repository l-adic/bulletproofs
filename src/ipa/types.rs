use ark_ec::CurveGroup;
use ark_ff::{Field, UniformRand};
use proptest::prelude::*;
use rand::rngs::OsRng;
use rayon::prelude::*;
use std::ops::{Add, Mul};

#[derive(Clone, Debug)]
pub struct Vector<Fr>(pub Vec<Fr>);

impl<Fr: Field> Vector<Fr> {
    pub fn rand(size: u64) -> Self {
        let mut v = Vec::new();
        for _ in 0..size {
            v.push(UniformRand::rand(&mut OsRng));
        }
        Vector(v)
    }
}

impl<Fr: Field> Vector<Fr> {
    pub fn add(&self, rhs: &Self) -> Vector<Fr> {
        let mut result = Vec::new();
        for (a, b) in self.0.iter().zip(rhs.0.iter()) {
            result.push(*a + *b);
        }
        Vector(result)
    }

    pub fn dot(&self, b: &Self) -> Fr {
        self.0
            .iter()
            .zip(b.0.iter())
            .fold(Fr::zero(), |acc, (x, y)| acc + (*x * *y))
    }
}

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
    pub fn rand(size: CrsSize) -> Self {
        let size = 1 << size.log2_size;
        let gs = (0..size)
            .into_par_iter()
            .map(|_| G::Affine::rand(&mut OsRng))
            .collect();
        let hs = (0..size)
            .into_par_iter()
            .map(|_| G::Affine::rand(&mut OsRng))
            .collect();
        let u = G::Affine::rand(&mut OsRng);
        CRS { gs, hs, u }
    }

    pub fn size(&self) -> usize {
        self.gs.len()
    }
}

#[derive(Clone, Debug)]
pub struct Witness<Fr> {
    pub a: Vector<Fr>,
    pub b: Vector<Fr>,
    c: Fr,
}

impl<Fr: Field> Witness<Fr> {
    pub fn new(a: Vector<Fr>, b: Vector<Fr>) -> Self {
        let c = a.dot(&b);
        Witness { a, b, c }
    }

    pub fn rand(size: u64) -> Self {
        let a = Vector::rand(size);
        let b = Vector::rand(size);
        let c = a.dot(&b);
        Witness { a, b, c }
    }

    pub fn c(&self) -> Fr {
        self.c
    }
}

impl<Fr: Field> Add for Witness<Fr> {
    type Output = Witness<Fr>;

    fn add(self, rhs: Self) -> Self::Output {
        Witness {
            a: self.a.add(&rhs.a),
            b: self.b.add(&rhs.b),
            c: self.c + rhs.c,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Statement<G> {
    pub p: G,
}

impl<G: CurveGroup> Add for Statement<G> {
    type Output = Statement<G>;

    fn add(self, rhs: Self) -> Self::Output {
        Statement { p: self.p + rhs.p }
    }
}

pub fn statement<G: CurveGroup>(crs: &CRS<G>, inputs: &Witness<G::ScalarField>) -> Statement<G> {
    let g: G = G::msm_unchecked(&crs.gs, &inputs.a.0);
    let h: G = G::msm_unchecked(&crs.hs, &inputs.b.0);
    let p: G = g.add(&h).add(&crs.u.mul(inputs.c));
    Statement { p }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_secp256k1::{self, Projective};
    use proptest::test_runner::Config;

    proptest! {
      #![proptest_config(Config::with_cases(2))]
      #[test]
      fn statements_are_additive((crs, inputs1, inputs2) in any::<CrsSize>().prop_map(|crs_size| {
          let crs: CRS<Projective> = CRS::rand(crs_size);
          let n = crs.size() as u64;
          let inputs1 = Witness::rand(n);
          let inputs2 = Witness::rand(n);
          (crs, inputs1, inputs2)
      })) {
          let c1 = statement(&crs, &inputs1);
          let c2 = statement(&crs, &inputs2);
          let c =  statement(&crs, &(inputs1 + inputs2));
          prop_assert!(c.p == c1.p + c2.p);
      }
    }
}
