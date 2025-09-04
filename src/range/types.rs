use crate::ipa::{self, types::CrsSize};
use ark_ec::CurveGroup;
use ark_ff::{BigInteger, Field, One, PrimeField};
use ark_std::log2;
use std::ops::Mul;

pub struct CRS<G: CurveGroup> {
    pub ipa_crs: ipa::types::CRS<G>,
    pub g: G::Affine,
    pub h: G::Affine,
    pub one_vec: Vec<G::ScalarField>,
    pub two_vec: Vec<G::ScalarField>,
}

impl<G: CurveGroup> CRS<G> {
    pub fn rand(n: usize) -> Self
where {
        let mut rng = &mut rand::thread_rng();
        let ipa_crs = {
            let log2_size = log2(n) as u64;
            ipa::types::CRS::rand(CrsSize { log2_size })
        };
        let g = G::rand(&mut rng).into_affine();
        let h = G::rand(&mut rng).into_affine();
        let one_vec: Vec<G::ScalarField> = vec![G::ScalarField::one(); n];
        let two_vec: Vec<G::ScalarField> = (0..n)
            .map(|i| G::ScalarField::from(2u64).pow([i as u64]))
            .collect();
        CRS {
            ipa_crs,
            g,
            h,
            one_vec,
            two_vec,
        }
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
