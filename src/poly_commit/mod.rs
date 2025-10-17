pub mod types;

use crate::{
    poly_commit::types::{CRS, PolyCommit, Statement, Witness},
    vector_ops::inner_product,
};
use ark_ec::CurveGroup;
use ark_ff::{Field, UniformRand, Zero, batch_inversion};
use ark_poly::{polynomial::DenseUVPolynomial, univariate::DensePolynomial};
use ark_std::log2;
use rayon::prelude::*;
use spongefish::{
    DomainSeparator, ProofResult, ProverState, VerifierState,
    codecs::arkworks_algebra::{
        FieldDomainSeparator, FieldToUnitDeserialize, FieldToUnitSerialize, GroupDomainSeparator,
        GroupToUnitDeserialize, GroupToUnitSerialize, UnitToField,
    },
};
use std::{marker::PhantomData, ops::Mul};

pub trait OpeningProofDomainSeparator<G: CurveGroup> {
    fn opening_proof_statement(self) -> Self;
    fn add_opening_proof(self, len: usize) -> Self;
}

impl<G> OpeningProofDomainSeparator<G> for DomainSeparator
where
    G: CurveGroup,
    Self: GroupDomainSeparator<G> + FieldDomainSeparator<G::ScalarField>,
{
    fn opening_proof_statement(self) -> Self {
        self.add_points(1, "commitment")
            .add_scalars(1, "point")
            .add_scalars(1, "evalutation")
    }

    fn add_opening_proof(mut self, len: usize) -> Self {
        self = self.challenge_scalars(1, "u_coeff");
        for _ in 0..log2(len) {
            self = self
                .add_points(2, "round-message")
                .challenge_scalars(1, "challenge");
        }
        self.add_scalars(2, "final-message")
    }
}

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

pub fn prove<G: CurveGroup, P: DenseUVPolynomial<G::ScalarField>, Rng: rand::Rng>(
    prover_state: &mut ProverState,
    crs: &CRS<G>,
    statement: &Statement<G>,
    witness: &Witness<G, P>,
    rng: &mut Rng,
) -> ProofResult<Todo<G>> {
    let u: G = {
        let [u_coeff]: [G::ScalarField; 1] = prover_state.challenge_scalars()?;
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

        prover_state.add_points(&[left_j, right_j])?;

        let [u_j]: [G::ScalarField; 1] = prover_state.challenge_scalars()?;
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

    prover_state.add_scalars(&[a[0], r])?;
    {
        let h_poly = HPoly { ui: ui.clone() };
        let ss = h_poly.coeffs();
        let g_comp = G::msm_unchecked(&crs.gs, &ss);
        assert_eq!(g[0], g_comp.into_affine(), "Gs NEQ")
    }

    Ok(Todo {
        g: PolyCommit { g: g[0].into() },
        h_poly: HPoly { ui },
    })
}

pub fn verify<G: CurveGroup>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
) -> ProofResult<()> {
    let n = crs.size();
    let log2_n = log2(n) as usize;

    let u: G = {
        let [u_coeff]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
        G::generator().mul(u_coeff)
    };

    let p_prime = statement.commitment.g + u.mul(statement.evaluation);

    let transcript = (0..log2_n)
        .map(|_| {
            let [left, right]: [G; 2] = verifier_state.next_points()?;
            let [x]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
            Ok(((left, right), x))
        })
        .collect::<ProofResult<Vec<_>>>()?;

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

    let [a, r]: [G::ScalarField; 2] = verifier_state.next_scalars()?;
    let res = g.mul(a) + crs.h.mul(r) + u.mul(a * b) - q;

    assert!(res.is_zero(), "Q equality");
    Ok(())
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

pub fn lazy_verify<G: CurveGroup>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
    assumption: PolyCommit<G>,
    mut todos: Vec<Todo<G>>,
) -> ProofResult<Vec<Todo<G>>> {
    let n = crs.size();
    let log2_n = log2(n) as usize;

    let u: G = {
        let [u_coeff]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
        G::generator().mul(u_coeff)
    };

    let p_prime = statement.commitment.g + u.mul(statement.evaluation);

    let transcript = (0..log2_n)
        .map(|_| {
            let [left, right]: [G; 2] = verifier_state.next_points()?;
            let [x]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
            Ok(((left, right), x))
        })
        .collect::<ProofResult<Vec<_>>>()?;

    let q: G = transcript.iter().fold(p_prime, |acc, ((l_j, r_j), u_j)| {
        let u_j_inv = u_j.inverse().expect("non zero u_j");
        acc + l_j.mul(u_j.square()) + r_j.mul(u_j_inv.square())
    });

    let h_poly = HPoly {
        ui: transcript.iter().map(|&(_, x)| x).collect(),
    };

    let b = h_poly.evaluate(statement.x);

    let [a, r]: [G::ScalarField; 2] = verifier_state.next_scalars()?;
    let res = assumption.g.mul(a) + crs.h.mul(r) + u.mul(a * b) - q;

    assert!(res.is_zero(), "Q equality");
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

#[cfg(test)]
mod tests_proof {
    use super::*;
    use crate::ipa::types::CrsSize;
    use ark_ec::PrimeGroup;
    use ark_poly::univariate::DensePolynomial;
    use ark_secp256k1::{self, Projective};
    use ark_std::UniformRand;
    use proptest::{prelude::*, test_runner::Config};
    use rand::rngs::OsRng;
    use spongefish::codecs::arkworks_algebra::{CommonFieldToUnit, CommonGroupToUnit};
    use spongefish::{DomainSeparator, ProofError};
    use std::ops::Add;

    type Fr =
        <ark_ec::short_weierstrass::Projective<ark_secp256k1::Config> as PrimeGroup>::ScalarField;

    pub fn prove_verify<G: CurveGroup>(
        crs: &CRS<G>,
        witness: &Witness<G, DensePolynomial<G::ScalarField>>,
        statement: &Statement<G>,
        rng: &mut OsRng,
    ) -> ProofResult<()> {
        let domain_separator = {
            let domain_separator = DomainSeparator::new("test-poly-comm");
            // add the IO of the bulletproof statement
            let domain_separator =
                OpeningProofDomainSeparator::<Projective>::opening_proof_statement(
                    domain_separator,
                )
                .ratchet();
            // add the IO of the bulletproof protocol (the transcript)
            OpeningProofDomainSeparator::<Projective>::add_opening_proof(
                domain_separator,
                witness.size(),
            )
        };

        let mut prover_state = domain_separator.to_prover_state();
        let proof = {
            prover_state
                .public_points(&[statement.commitment.g])
                .unwrap();
            prover_state.public_scalars(&[statement.x]).unwrap();
            prover_state
                .public_scalars(&[statement.evaluation])
                .unwrap();
            prover_state.ratchet().unwrap();
            prove(&mut prover_state, crs, statement, witness, rng)
                .expect("proof should be generated");
            prover_state.narg_string()
        };

        let mut verifier_state = domain_separator.to_verifier_state(proof);
        verifier_state
            .public_points(&[statement.commitment.g])
            .expect("cannot add statement");
        verifier_state
            .public_scalars(&[statement.x])
            .expect("cannot add statement");
        verifier_state
            .public_scalars(&[statement.evaluation])
            .expect("cannot add statement");
        verifier_state.ratchet().expect("failed to ratchet");
        verify(&mut verifier_state, crs, statement)
    }

    proptest! {
      #![proptest_config(Config::with_cases(2))]
      #[test]
      fn test_poly_comm_prove_verify_works((crs, witness1, witness2, statement1, statement2) in any::<CrsSize>().prop_map(|crs_size| {
          let mut rng = OsRng;
          let crs = <CRS<Projective>>::rand(crs_size, &mut rng);
          let n = crs.size() as u64;
          let witness1: Witness<Projective, DensePolynomial<Fr>> = Witness::rand((n - 1) as usize, &mut rng);
          let witness2: Witness<Projective, DensePolynomial<Fr>> = Witness::rand((n - 1) as usize, &mut rng);
          let x = Fr::rand(&mut rng);
          let statement1 = witness1.statement(&crs,x);
          let statement2 = witness2.statement(&crs,x);
          (crs, witness1, witness2, statement1, statement2)
      })) {
            let mut rng = OsRng;

            // works in normal case
            prove_verify(&crs, &witness1, &statement1, &mut rng).expect("normal");

            //can scale
            let alpha1 = Fr::rand(&mut rng);
            let alpha2 = Fr::rand(&mut rng);
            let witness = witness1.mul(alpha1).add(witness2.mul(alpha2));
            let statement = statement1.mul(alpha1).add(statement2.mul(alpha2));
            assert_eq!(statement, witness.statement(&crs, statement1.x), "statements are linear");
            prove_verify(&crs, &witness, &statement, &mut rng).expect("linear");


      }
    }

    proptest! {
      #![proptest_config(Config::with_cases(2))]
      #[test]
      fn test_poly_comm_amortize((crs, witnesses, points) in any::<(CrsSize, u8)>().prop_map(|(crs_size, _)| {
          let mut rng = OsRng;
          let crs = <CRS<Projective>>::rand(crs_size, &mut rng);
          let n = crs.size() as u64;
          let m = 4;

          let witnesses = {
            let mut ws = Vec::with_capacity(m as usize);
            for _ in 0..m {
                ws.push(<Witness<Projective, DensePolynomial<Fr>>>::rand((n - 1) as usize, &mut rng));
            };
            ws
          };

          let points: Vec<Fr> = (0..witnesses.len()).map(|_|  Fr::rand(&mut rng)).collect();

          (crs, witnesses, points)
      })) {
            let mut rng = OsRng;
            let domain_separator = DomainSeparator::new("test-poly-comm");

            let proofs = points.iter().zip(witnesses.iter()).map(|(&x, witness)| {
                let domain_separator = OpeningProofDomainSeparator::<Projective>::opening_proof_statement(domain_separator.clone()).ratchet();
                let domain_separator = OpeningProofDomainSeparator::<Projective>::add_opening_proof(domain_separator, crs.size());
                let mut prover_state = domain_separator.to_prover_state();
                let statement = witness.statement(&crs, x);
                prover_state
                    .public_points(&[statement.commitment.g])
                    .unwrap();
                prover_state.public_scalars(&[statement.x]).unwrap();
                prover_state
                    .public_scalars(&[statement.evaluation])
                    .unwrap();
                prover_state.ratchet().unwrap();
                let proof = prove(&mut prover_state, &crs, &statement, witness, &mut rng)?;
                Ok((domain_separator, prover_state.narg_string().to_vec(), statement, proof))
            }).collect::<Result<Vec<_>, ProofError>>()?;

            let verifier_todos = proofs.iter().try_fold(Vec::new(), |todos, (domain_separator, proof, statement, prover_todo)| {
                let mut verifier_state = domain_separator.to_verifier_state(proof);
                verifier_state
                    .public_points(&[statement.commitment.g])
                    .expect("cannot add statement");
                verifier_state
                    .public_scalars(&[statement.x])
                    .expect("cannot add statement");
                verifier_state
                    .public_scalars(&[statement.evaluation])
                    .expect("cannot add statement");
                verifier_state.ratchet().expect("failed to ratchet");
                lazy_verify(&mut verifier_state, &crs, statement, prover_todo.g, todos)
            })?;

            let prover_todos: Vec<Todo<Projective>> = proofs.iter().map(|(_,_,_,todo)| todo).cloned().collect();

            assert_eq!(prover_todos, verifier_todos, "Prover todos don't match verifier todos");

            let alpha = Fr::rand(&mut rng);
            let x = Fr::rand(&mut rng);
            let witness = fold_todos_witness(&prover_todos, alpha);
            let statement = fold_todos_statement(&verifier_todos, alpha, x);
            {
                let prover_statement = witness.statement(&crs, x);
                assert_eq!(prover_statement, statement, "Statements match");
            }

            prove_verify(&crs, &witness, &statement, &mut rng)?;
      }
    }
}
