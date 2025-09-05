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

pub struct Statement<G: CurveGroup> {
    pub v: Vec<G>,
}

impl<G: CurveGroup> Statement<G> {
    pub fn new(crs: &CRS<G>, witness: &Witness<G::ScalarField>) -> Self {
        Statement {
            v: witness
                .v
                .iter()
                .zip(witness.gamma.iter())
                .map(|(vi, gi)| crs.g.mul(*vi) + crs.h.mul(*gi))
                .collect::<Vec<_>>(),
        }
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

    pub fn is_satisfied_by(&self, witness: &Witness<Fr>) -> bool
    where
        Fr: Field,
    {
        use crate::circuit::utils::hadarmard;
        use crate::ipa::utils::dot;

        // Check arithmetic constraint: a_l ⊙ a_r = a_o
        let expected_a_o = hadarmard(&witness.a_l, &witness.a_r);
        if witness.a_o != expected_a_o {
            return false;
        }

        // Check circuit constraints: W_l * a_l + W_r * a_r + W_o * a_o = W_v * v + c
        for i in 0..self.size() {
            let lhs = dot(&self.w_l[i], &witness.a_l)
                + dot(&self.w_r[i], &witness.a_r)
                + dot(&self.w_o[i], &witness.a_o);
            let rhs = dot(&self.w_v[i], &witness.v) + self.c[i];
            if lhs != rhs {
                return false;
            }
        }

        true
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

    #[cfg(test)]
    pub fn generate_from_witness<Rng: rand::Rng>(
        q: usize,
        n: usize,
        rng: &mut Rng,
    ) -> (Self, Witness<Fr>)
    where
        Fr: Field + UniformRand,
    {
        use crate::circuit::utils::hadarmard;
        use crate::ipa::utils::dot;

        // Step 1: Generate witness with arithmetic constraint a_l * a_r = a_o
        let a_l: Vec<Fr> = (0..n).map(|_| Fr::rand(rng)).collect();
        let a_r: Vec<Fr> = (0..n).map(|_| Fr::rand(rng)).collect();
        let a_o = hadarmard(&a_l, &a_r); // a_l ⊙ a_r = a_o

        // Step 2: Generate random v (auxiliary witness)
        let v: Vec<Fr> = (0..n).map(|_| Fr::rand(rng)).collect();

        // Step 3: Generate random constraint matrices W_l, W_r, W_o, W_v
        let w_l: Vec<Vec<Fr>> = (0..q)
            .map(|_| (0..n).map(|_| Fr::rand(rng)).collect())
            .collect();
        let w_r: Vec<Vec<Fr>> = (0..q)
            .map(|_| (0..n).map(|_| Fr::rand(rng)).collect())
            .collect();
        let w_o: Vec<Vec<Fr>> = (0..q)
            .map(|_| (0..n).map(|_| Fr::rand(rng)).collect())
            .collect();
        let w_v: Vec<Vec<Fr>> = (0..q)
            .map(|_| (0..n).map(|_| Fr::rand(rng)).collect())
            .collect();

        // Step 4: Compute c to satisfy constraints: W_l * a_l + W_r * a_r + W_o * a_o = W_v * v + c
        let c: Vec<Fr> = (0..q)
            .map(|i| {
                let lhs = dot(&w_l[i], &a_l) + dot(&w_r[i], &a_r) + dot(&w_o[i], &a_o);
                let rhs_wv = dot(&w_v[i], &v);
                lhs - rhs_wv // c[i] = lhs - W_v[i] * v
            })
            .collect();

        let circuit = Self::new(w_l, w_r, w_o, w_v, c);
        let witness = Witness::new(a_l, a_r, a_o, v, rng);

        (circuit, witness)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::utils::hadarmard;
    use crate::ipa::utils::dot;
    use ark_secp256k1::Fr;
    use rand::rngs::OsRng;

    #[test]
    fn test_generate_from_witness_satisfies_constraints() {
        let mut rng = OsRng;
        let q = 4;
        let n = 6;

        let (circuit, witness) = Circuit::<Fr>::generate_from_witness(q, n, &mut rng);

        // Verify arithmetic constraint: a_l ⊙ a_r = a_o
        let expected_a_o = hadarmard(&witness.a_l, &witness.a_r);
        assert_eq!(
            witness.a_o, expected_a_o,
            "Arithmetic constraint a_l ⊙ a_r = a_o not satisfied"
        );

        // Verify circuit constraint: W_l * a_l + W_r * a_r + W_o * a_o = W_v * v + c
        for i in 0..q {
            let lhs = dot(&circuit.w_l[i], &witness.a_l)
                + dot(&circuit.w_r[i], &witness.a_r)
                + dot(&circuit.w_o[i], &witness.a_o);
            let rhs = dot(&circuit.w_v[i], &witness.v) + circuit.c[i];
            assert_eq!(lhs, rhs, "Circuit constraint {} not satisfied", i);
        }
    }
}
