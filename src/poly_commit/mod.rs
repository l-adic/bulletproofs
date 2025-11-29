pub mod types;

use crate::{
    poly_commit::types::{CRS, PolyCommit, Statement, Witness},
    vector_ops::inner_product,
};
use ark_ec::{CurveGroup, PrimeGroup};
use ark_ff::{Field, UniformRand, Zero, batch_inversion};
use ark_poly::{polynomial::DenseUVPolynomial, univariate::DensePolynomial};
use ark_std::log2;
use rayon::prelude::*;
use spongefish::{
    Codec, Encoding, NargDeserialize, ProverState, VerificationError, VerificationResult,
    VerifierState,
};
use std::{marker::PhantomData, ops::Mul};

// pub trait OpeningProofDomainSeparator<G: CurveGroup> {
//     fn opening_proof_statement(self) -> Self;
//     fn add_opening_proof(self, len: usize) -> Self;
// }

// impl<G> OpeningProofDomainSeparator<G> for DomainSeparator
// where
//     G: CurveGroup,
//     Self: GroupDomainSeparator<G> + FieldDomainSeparator<G::ScalarField>,
// {
//     fn opening_proof_statement(self) -> Self {
//         self.add_points(1, "commitment")
//             .add_scalars(1, "point")
//             .add_scalars(1, "evalutation")
//     }

//     fn add_opening_proof(mut self, len: usize) -> Self {
//         self = self.challenge_scalars(1, "u_coeff");
//         for _ in 0..log2(len) {
//             self = self
//                 .add_points(2, "round-message")
//                 .challenge_scalars(1, "challenge");
//         }
//         self.add_scalars(2, "final-message")
//     }
// }

fn powers_of_x<F: Field>(x: F) -> impl Iterator<Item = F> {
    (0..).scan(F::one(), move |state, _| {
        let current = *state;
        *state = state.mul(x);
        Some(current)
    })
}

fn fold_scalars<Fr: Field>(left: &[Fr], x: Fr, right: &[Fr], y: Fr) -> Vec<Fr> {
    left.par_iter()
        .zip(right)
        .map(|(l, r)| *l * x + *r * y)
        .collect::<Vec<_>>()
}

fn fold_generators<G: CurveGroup>(
    left: &[G::Affine],
    x: G::ScalarField,
    right: &[G::Affine],
    y: G::ScalarField,
) -> Vec<G::Affine> {
    let gs: Vec<G> = left
        .par_iter()
        .zip(right)
        .map(|(l, r)| l.mul(x) + r.mul(y))
        .collect();
    G::normalize_batch(&gs)
}

pub fn prove<G: CurveGroup + Encoding, P: DenseUVPolynomial<G::ScalarField>, Rng: rand::Rng>(
    prover_state: &mut ProverState,
    crs: &CRS<G>,
    statement: &Statement<G>,
    witness: &Witness<G, P>,
    rng: &mut Rng,
) -> Todo<G>
where
    <G as PrimeGroup>::ScalarField: Codec,
{
    let u: G = {
        let u_coeff: G::ScalarField = prover_state.verifier_message();
        G::generator().mul(u_coeff)
    };

    let mut r = witness.r;

    let mut n = witness.size();
    let mut g = crs.gs.clone();
    let mut a: Vec<G::ScalarField> = witness.p.coeffs().to_vec();
    let mut b: Vec<G::ScalarField> = powers_of_x(statement.x).take(n).collect();

    let mut ui: Vec<G::ScalarField> = Vec::with_capacity(log2(n) as usize);

    while n != 1 {
        n /= 2;
        let (g_lo, g_hi) = g.split_at(n);
        let (a_lo, a_hi) = a.split_at(n);
        let (b_lo, b_hi) = b.split_at(n);

        let (l_j, r_j) = (G::ScalarField::rand(rng), G::ScalarField::rand(rng));
        let (left_j, right_j): (G, G) = rayon::join(
            || {
                G::msm_unchecked(g_hi, a_lo)
                    + crs.h.mul(l_j)
                    + u.mul(inner_product::<_, _, G::ScalarField>(a_lo, b_hi))
            },
            || {
                G::msm_unchecked(g_lo, a_hi)
                    + crs.h.mul(r_j)
                    + u.mul(inner_product::<_, _, G::ScalarField>(a_hi, b_lo))
            },
        );

        prover_state.prover_messages(&[left_j, right_j]);

        let u_j: G::ScalarField = prover_state.verifier_message();
        ui.push(u_j);
        let u_j_inv = u_j.inverse().expect("non-zero u_j");

        let (new_a, new_b) = rayon::join(
            || fold_scalars(a_hi, u_j_inv, a_lo, u_j),
            || fold_scalars(b_lo, u_j_inv, b_hi, u_j),
        );
        a = new_a;
        b = new_b;

        g = fold_generators::<G>(g_lo, u_j_inv, g_hi, u_j);

        r += l_j * u_j.square() + r_j * u_j_inv.square();
    }

    prover_state.prover_messages(&[a[0], r]);
    {
        let h_poly = HPoly { ui: ui.clone() };
        let ss = h_poly.coeffs();
        let g_comp = G::msm_unchecked(&crs.gs, &ss);
        assert_eq!(g[0], g_comp.into_affine(), "Gs NEQ")
    }

    Todo {
        g: PolyCommit { g: g[0].into() },
        h_poly: HPoly { ui },
    }
}

pub fn verify<G: CurveGroup + Encoding + NargDeserialize>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
) -> VerificationResult<()>
where
    <G as PrimeGroup>::ScalarField: Codec,
{
    let n = crs.size();
    let log2_n = log2(n) as usize;

    let u: G = {
        let u_coeff: G::ScalarField = verifier_state.verifier_message();
        G::generator().mul(u_coeff)
    };

    let p_prime = statement.commitment.g + u.mul(statement.evaluation);

    let transcript = (0..log2_n)
        .map(|_| -> VerificationResult<((G, G), G::ScalarField)> {
            let [left, right]: [G; 2] = verifier_state.prover_messages()?;
            let x: G::ScalarField = verifier_state.verifier_message();
            Ok(((left, right), x))
        })
        .collect::<VerificationResult<Vec<_>>>()?;

    let q: G = transcript.iter().fold(p_prime, |acc, ((l_j, r_j), u_j)| {
        let u_j_inv = u_j.inverse().expect("non zero u_j");
        acc + l_j.mul(u_j.square()) + r_j.mul(u_j_inv.square())
    });

    let ss: Vec<G::ScalarField> = {
        let h_poly = HPoly {
            ui: transcript.iter().map(|&(_, x)| x).collect(),
        };
        h_poly.coeffs()
    };

    let g = G::msm_unchecked(&crs.gs, &ss);
    let b = {
        let b = powers_of_x(statement.x).take(n);
        inner_product(ss, b)
    };

    let [a, r]: [G::ScalarField; 2] = verifier_state.prover_messages()?;
    let res = g.mul(a) + crs.h.mul(r) + u.mul(a * b) - q;

    if res.is_zero() {
        Ok(())
    } else {
        Err(VerificationError)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct HPoly<F> {
    pub ui: Vec<F>,
}

impl<F: Field> HPoly<F> {
    pub fn evaluate(&self, x: F) -> F {
        self.ui
            .iter()
            .rev()
            .enumerate()
            .map(|(i, &u_i)| {
                let u_i_inv = u_i.inverse().unwrap();
                let exp = 2_u64.pow(i as u32);
                u_i_inv + u_i * x.pow([exp])
            })
            .product()
    }

    pub fn coeffs(&self) -> Vec<F> {
        let ui_inverses = {
            let mut inverses = self.ui.clone();
            batch_inversion(&mut inverses);
            inverses
        };

        let k = self.ui.len();
        let n = (2_u64).pow(k as u32);

        (0..n)
            .into_par_iter()
            .map(|i| {
                (0..k)
                    .map(|j| {
                        let idx = k - j - 1;
                        if (i >> j) & 1 == 1 {
                            self.ui[idx]
                        } else {
                            ui_inverses[idx]
                        }
                    })
                    .product()
            })
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Todo<G: CurveGroup> {
    pub h_poly: HPoly<G::ScalarField>,
    pub g: PolyCommit<G>,
}

pub fn fold_todos_witness<G: CurveGroup>(
    todos: &[Todo<G>],
    alpha: G::ScalarField,
) -> Witness<G, DensePolynomial<G::ScalarField>> {
    todos
        .iter()
        .map(|Todo { h_poly, .. }| Witness {
            // It is important to put zero for the amortization, i.e. "Halo Trick"
            r: G::ScalarField::zero(),
            p: DensePolynomial::from_coefficients_vec(h_poly.coeffs()),
            _group: PhantomData,
        })
        .zip(powers_of_x(alpha))
        .map(|(witness, alpha_i)| witness.mul(alpha_i))
        .reduce(|x, y| x + y)
        .expect("Non empty statement list")
}

pub fn fold_todos_statement<G: CurveGroup>(
    todos: &[Todo<G>],
    alpha: G::ScalarField,
    x: G::ScalarField,
) -> Statement<G> {
    todos
        .iter()
        .map(|Todo { h_poly, g }| Statement {
            commitment: *g,
            evaluation: h_poly.evaluate(x),
            x,
        })
        .zip(powers_of_x(alpha))
        .map(|(s, alpha_i)| s.mul(alpha_i))
        .reduce(|x, y| x + y)
        .expect("Non empty statement list")
}

pub fn lazy_verify<G: CurveGroup + Encoding + NargDeserialize>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
    assumption: PolyCommit<G>,
    mut todos: Vec<Todo<G>>,
) -> VerificationResult<Vec<Todo<G>>>
where
    <G as PrimeGroup>::ScalarField: Codec,
{
    let n = crs.size();
    let log2_n = log2(n) as usize;

    let u: G = {
        let u_coeff: G::ScalarField = verifier_state.verifier_message();
        G::generator().mul(u_coeff)
    };

    let p_prime = statement.commitment.g + u.mul(statement.evaluation);

    let transcript = (0..log2_n)
        .map(|_| -> VerificationResult<((G, G), G::ScalarField)> {
            let [left, right]: [G; 2] = verifier_state.prover_messages()?;
            let x: G::ScalarField = verifier_state.verifier_message();
            Ok(((left, right), x))
        })
        .collect::<VerificationResult<Vec<_>>>()?;

    let q: G = transcript.iter().fold(p_prime, |acc, ((l_j, r_j), u_j)| {
        let u_j_inv = u_j.inverse().expect("non zero u_j");
        acc + l_j.mul(u_j.square()) + r_j.mul(u_j_inv.square())
    });

    let h_poly = HPoly {
        ui: transcript.iter().map(|&(_, x)| x).collect(),
    };

    let b = h_poly.evaluate(statement.x);

    let [a, r]: [G::ScalarField; 2] = verifier_state.prover_messages()?;
    let res = assumption.g.mul(a) + crs.h.mul(r) + u.mul(a * b) - q;

    if !res.is_zero() {
        return Err(VerificationError);
    }
    let todo = Todo {
        g: assumption,
        h_poly,
    };
    todos.push(todo);
    Ok(todos)
}

#[cfg(test)]
mod test_hpoly {
    use super::*;
    use ark_secp256k1::Fr;
    use ark_std::UniformRand;
    use rand::rngs::OsRng;

    #[test]
    fn test_hpoly_evaluation_matches_expansion() {
        let mut rng = OsRng;

        // Test with a small HPoly
        let ui: Vec<Fr> = (0..3).map(|_| Fr::rand(&mut rng)).collect();
        let h_poly = HPoly { ui };
        let x = Fr::rand(&mut rng);

        // Compute via efficient evaluate method
        let eval_result = h_poly.evaluate(x);

        // Compute via expansion and inner product
        let coeffs = h_poly.coeffs();
        let n = coeffs.len();
        let x_powers: Vec<Fr> = powers_of_x(x).take(n).collect();
        let inner_result = inner_product(coeffs, x_powers);

        assert_eq!(
            eval_result, inner_result,
            "HPoly evaluation mismatch: eval={:?}, inner={:?}",
            eval_result, inner_result
        );
    }
}

// #[cfg(test)]
// mod tests_proof {
// Tests commented out - need to be updated for new spongefish API
