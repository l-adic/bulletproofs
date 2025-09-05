use ark_ec::CurveGroup;
use ark_ff::{Field, UniformRand};
use ark_std::log2;

use crate::ipa::types::CrsSize;

pub struct CRS<G: CurveGroup> {
    pub ipa_crs: crate::ipa::types::CRS<G>,
    pub g: G,
    pub h: G,
}

impl<G: CurveGroup> CRS<G> {
    pub fn rand(n: usize) -> Self {
        let mut rng = &mut rand::thread_rng();
        let ipa_crs = {
            let n = CrsSize {
                log2_size: log2(n) as u64,
            };
            crate::ipa::types::CRS::rand(n)
        };
        let g = G::rand(&mut rng);
        let h = G::rand(&mut rng);
        CRS { ipa_crs, g, h }
    }

    pub fn size(&self) -> usize {
        self.ipa_crs.size()
    }
}

pub struct Witness<Fr> {
    pub a_l: Vec<Fr>,
    pub a_r: Vec<Fr>,
    pub a_o: Vec<Fr>,
    pub v: Vec<Fr>,
    pub gamma: Vec<Fr>,
}

impl<Fr: Field> Witness<Fr> {
    pub fn new<Rng: rand::Rng>(
        a_l: Vec<Fr>,
        a_r: Vec<Fr>,
        a_o: Vec<Fr>,
        v: Vec<Fr>,
        rng: &mut Rng,
    ) -> Self {
        let gamma = (0..a_l.len()).map(|_| Fr::rand(rng)).collect();
        Self {
            a_l,
            a_r,
            a_o,
            v,
            gamma,
        }
    }

    pub fn rand<Rng: rand::Rng>(n: usize, rng: &mut Rng) -> Self {
        let a_l = (0..n).map(|_| Fr::rand(rng)).collect();
        let a_r = (0..n).map(|_| Fr::rand(rng)).collect();
        let a_o = (0..n).map(|_| Fr::rand(rng)).collect();
        let v = (0..n).map(|_| Fr::rand(rng)).collect();
        let gamma = (0..n).map(|_| Fr::rand(rng)).collect();
        Self {
            a_l,
            a_r,
            a_o,
            v,
            gamma,
        }
    }

    pub fn size(&self) -> usize {
        self.a_l.len()
    }
}

pub struct Circuit<Fr> {
    // row vectors, i.r. w_l[i] is the i-th row
    pub w_l: Vec<Vec<Fr>>,
    pub w_r: Vec<Vec<Fr>>,
    pub w_o: Vec<Vec<Fr>>,
    pub w_v: Vec<Vec<Fr>>,
    pub c: Vec<Fr>,
}

impl<Fr> Circuit<Fr> {
    pub fn new(
        w_l: Vec<Vec<Fr>>,
        w_r: Vec<Vec<Fr>>,
        w_o: Vec<Vec<Fr>>,
        w_v: Vec<Vec<Fr>>,
        c: Vec<Fr>,
    ) -> Self {
        let q = w_l.len();
        assert!(q > 0, "circuit cannot be empty");
        assert!(
            w_r.len() == q && w_o.len() == q && w_v.len() == q && c.len() == q,
            "weights must have the same number of rows"
        );
        assert!(!w_l[0].is_empty(), "circuit cannot be empty");
        let n = w_l[0].len();
        for i in 0..q {
            assert!(
                w_l[i].len() == n && w_r[i].len() == n && w_o[i].len() == n && w_v[i].len() == n,
                "all rows must have the same dimension"
            );
        }
        Self {
            w_l,
            w_r,
            w_o,
            w_v,
            c,
        }
    }

    pub fn size(&self) -> usize {
        self.w_l.len()
    }

    pub fn dim(&self) -> usize {
        self.w_l[0].len()
    }

    pub fn rand<Rng: rand::Rng>(q: usize, n: usize, rng: &mut Rng) -> Self
    where
        Fr: UniformRand,
    {
        let w_l = (0..q)
            .map(|_| (0..n).map(|_| Fr::rand(rng)).collect())
            .collect();
        let w_r = (0..q)
            .map(|_| (0..n).map(|_| Fr::rand(rng)).collect())
            .collect();
        let w_o = (0..q)
            .map(|_| (0..n).map(|_| Fr::rand(rng)).collect())
            .collect();
        let w_v = (0..q)
            .map(|_| (0..n).map(|_| Fr::rand(rng)).collect())
            .collect();
        let c = (0..q).map(|_| Fr::rand(rng)).collect();
        Self::new(w_l, w_r, w_o, w_v, c)
    }
}
