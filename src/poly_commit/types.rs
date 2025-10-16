use ark_ec::CurveGroup;
use ark_ff::Zero;
use ark_poly::{DenseUVPolynomial, polynomial};
use std::marker::PhantomData;

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

#[derive(Debug, Clone, Copy)]
pub struct PolyCommit<G: CurveGroup> {
    pub g: G,
}

#[derive(Debug, Clone, Copy)]
pub struct Witness<G: CurveGroup, P: DenseUVPolynomial<G::ScalarField>> {
    pub p: P,
    pub r: G::ScalarField,
    _group: PhantomData<G>,
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
}

impl<G: CurveGroup, P: DenseUVPolynomial<G::ScalarField>> Witness<G, P> {
    pub fn size(&self) -> usize {
        self.p.degree() + 1
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Statement<G: CurveGroup> {
    pub commitment: PolyCommit<G>,
    pub x: G::ScalarField,
    pub evaluation: G::ScalarField,
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
