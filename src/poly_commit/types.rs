use ark_ec::CurveGroup;
use ark_ff::Zero;
use ark_poly::{DenseUVPolynomial, polynomial};
use std::marker::PhantomData;
use std::ops::{Add, Mul};

use crate::ipa::types::CrsSize;

#[derive(Debug)]
pub struct CRS<G: CurveGroup> {
    pub gs: Vec<G::Affine>,
    pub h: G,
}

impl<G: CurveGroup> CRS<G> {
    pub fn size(&self) -> usize {
        self.gs.len()
    }

    pub fn rand<Rng: rand::Rng>(size: CrsSize, rng: &mut Rng) -> CRS<G> {
        let n = 1 << size.log2_size;
        let gs = (0..n)
            .map(|_| G::rand(rng).into_affine())
            .collect::<Vec<_>>();
        let h = G::rand(rng);
        CRS { gs, h }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct PolyCommit<G: CurveGroup> {
    pub g: G,
}

impl<G: CurveGroup> PolyCommit<G> {
    #[allow(clippy::should_implement_trait)]
    pub fn mul(self, alpha: G::ScalarField) -> Self {
        Self {
            g: self.g.mul(alpha),
        }
    }
}

impl<G: CurveGroup> Add for PolyCommit<G> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        PolyCommit {
            g: self.g + other.g,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Witness<G: CurveGroup, P: DenseUVPolynomial<G::ScalarField>> {
    pub p: P,
    pub r: G::ScalarField,
    pub _group: PhantomData<G>,
}

impl<G: CurveGroup> Witness<G, polynomial::univariate::DensePolynomial<G::ScalarField>> {
    pub fn rand<Rng: rand::Rng>(degree: usize, rng: &mut Rng) -> Self {
        let p = polynomial::univariate::DensePolynomial::rand(degree, rng);
        let r = {
            use ark_ff::UniformRand;
            G::ScalarField::rand(rng)
        };
        Witness {
            p,
            r,
            _group: PhantomData,
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn mul(self, alpha: G::ScalarField) -> Self {
        Self {
            p: self.p.mul(alpha),
            r: self.r * alpha,
            _group: self._group,
        }
    }
}

impl<G: CurveGroup, P: DenseUVPolynomial<G::ScalarField>> Add for Witness<G, P> {
    type Output = Witness<G, P>;
    fn add(self, other: Self) -> Self {
        Self {
            p: self.p + other.p,
            r: self.r + other.r,
            _group: self._group,
        }
    }
}

impl<G: CurveGroup, P: DenseUVPolynomial<G::ScalarField>> Witness<G, P> {
    pub fn size(&self) -> usize {
        self.p.degree() + 1
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Statement<G: CurveGroup> {
    pub commitment: PolyCommit<G>,
    pub x: G::ScalarField,
    pub evaluation: G::ScalarField,
}

impl<G: CurveGroup> Statement<G> {
    #[allow(clippy::should_implement_trait)]
    pub fn mul(self, alpha: G::ScalarField) -> Self {
        Self {
            commitment: self.commitment.mul(alpha),
            x: self.x,
            evaluation: self.evaluation * alpha,
        }
    }
}

impl<G: CurveGroup> Add for Statement<G> {
    type Output = Statement<G>;
    fn add(self, other: Self) -> Self {
        assert!(
            self.x == other.x,
            "Can only add Statements where the evaluation points match"
        );
        Self {
            commitment: self.commitment + other.commitment,
            x: self.x,
            evaluation: self.evaluation + other.evaluation,
        }
    }
}

impl<G: CurveGroup, P: DenseUVPolynomial<G::ScalarField>> Witness<G, P> {
    pub fn statement(&self, crs: &CRS<G>, x: G::ScalarField) -> Statement<G> {
        let commitment = {
            let mut coeffs = self.p.coeffs().to_vec();
            coeffs.resize(crs.size(), G::ScalarField::zero());
            let g = G::msm_unchecked(&crs.gs, &coeffs);
            let blinder: G = crs.h.mul(self.r);
            PolyCommit { g: g.add(blinder) }
        };
        let evaluation = self.p.evaluate(&x);
        Statement {
            commitment,
            evaluation,
            x,
        }
    }
}
