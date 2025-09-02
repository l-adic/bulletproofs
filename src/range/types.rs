use ark_ec::CurveGroup;
use ark_ff::{BigInteger, Field, One, PrimeField};
use std::ops::Mul;

pub struct CRS<G: CurveGroup> {
    pub gs: Vec<G::Affine>,
    pub hs: Vec<G::Affine>,
    pub g: G::Affine,
    pub h: G::Affine,
    pub one_vec: Vec<G::ScalarField>,
    pub two_vec: Vec<G::ScalarField>,
}

impl<G: CurveGroup> CRS<G> {
    pub fn rand(n: usize) -> Self
where {
        let mut rng = &mut rand::thread_rng();
        let gs: Vec<G::Affine> = (0..n).map(|_| G::rand(&mut rng).into_affine()).collect();
        let hs: Vec<G::Affine> = (0..n).map(|_| G::rand(&mut rng).into_affine()).collect();
        let g = G::rand(&mut rng).into_affine();
        let h = G::rand(&mut rng).into_affine();
        let one_vec: Vec<G::ScalarField> = vec![G::ScalarField::one(); n];
        let two_vec: Vec<G::ScalarField> = (0..n)
            .map(|i| G::ScalarField::from(2u64).pow([i as u64]))
            .collect();
        CRS {
            gs,
            hs,
            g,
            h,
            one_vec,
            two_vec,
        }
    }

    pub fn size(&self) -> usize {
        self.gs.len()
    }
}

pub struct Witness<const N: usize, Fr> {
    pub v: Fr,
    pub gamma: Fr,
}

impl<Fr: PrimeField, const N: usize> Witness<N, Fr> {
    pub fn new<Rng: rand::Rng>(v: Fr, rng: &mut Rng) -> Self {
        assert!(v.into_bigint().num_bits() as usize <= N);
        Witness {
            v,
            gamma: Fr::rand(rng),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Statement<const N: usize, G> {
    pub v: G,
}

impl<G: CurveGroup, const N: usize> Statement<N, G> {
    pub fn new(crs: &CRS<G>, witness: &Witness<N, G::ScalarField>) -> Self {
        Statement {
            v: crs.g.mul(witness.v) + crs.h.mul(witness.gamma),
        }
    }
}
