pub mod types;

use crate::{
    poly_commit::types::{CRS, PolyCommit, Statement, Witness},
    vector_ops::inner_product,
};
use ark_ec::CurveGroup;
use ark_ff::{Field, UniformRand, batch_inversion};
use ark_poly::polynomial::DenseUVPolynomial;
use ark_std::log2;
use rayon::prelude::*;
use spongefish::{
    DomainSeparator, ProofResult, ProverState, VerifierState,
    codecs::arkworks_algebra::{
        FieldDomainSeparator, FieldToUnitDeserialize, FieldToUnitSerialize, GroupDomainSeparator,
        GroupToUnitDeserialize, GroupToUnitSerialize, UnitToField,
    },
};
use std::ops::{Add, Mul};

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
) -> ProofResult<Assumption<G>> {
    let u: G = {
        let [u_coeff]: [G::ScalarField; 1] = prover_state.challenge_scalars()?;
        G::generator().mul(u_coeff)
    };

    let mut r = witness.r;

    let mut n = witness.size();
    let mut g = crs.gs.clone();
    let mut a: Vec<G::ScalarField> = witness.p.coeffs().to_vec();
    let mut b: Vec<G::ScalarField> = powers_of_x(statement.x).take(n).collect();

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
    Ok(Assumption(PolyCommit { g: g[0].into() }))
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
        let challenge_powers: Vec<G::ScalarField> = transcript.iter().map(|&(_, x)| x).collect();
        let challenge_inverses = {
            let mut inverses = challenge_powers.clone();
            batch_inversion(&mut inverses);
            inverses
        };

        (0..n)
            .into_par_iter()
            .map(|i| {
                (0..log2_n)
                    .map(|j| {
                        let idx = log2_n - j - 1;
                        if (i >> j) & 1 == 1 {
                            challenge_powers[idx]
                        } else {
                            challenge_inverses[idx]
                        }
                    })
                    .product()
            })
            .collect()
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

pub struct HPoly<F> {
    pub ui: Vec<F>,
}

impl<F: Field> HPoly<F> {
    pub fn evaluate(&self, x: F) -> F {
        self.ui
            .iter()
            .enumerate()
            .map(|(i, &u)| u + u.inverse().unwrap() * x.pow([2_u64.pow((i as u32) - 1)]))
            .product()
    }
}

pub struct Assumption<G: CurveGroup>(PolyCommit<G>);

pub struct Todo<G: CurveGroup> {
    pub h_poly: HPoly<G::ScalarField>,
    pub g: PolyCommit<G>,
}

pub fn fold_todos<G: CurveGroup>(
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
        .reduce(Add::<Statement<G>>::add)
        .expect("Non empty statement list")
}

pub fn lazy_verify<G: CurveGroup>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
    assumption: Assumption<G>,
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
    let res = assumption.0.g.mul(a) + crs.h.mul(r) + u.mul(a * b) - q;

    assert!(res.is_zero(), "Q equality");
    let todo = Todo {
        g: assumption.0,
        h_poly,
    };
    todos.push(todo);
    Ok(todos)
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
    use spongefish::DomainSeparator;
    use spongefish::codecs::arkworks_algebra::{CommonFieldToUnit, CommonGroupToUnit};
    use std::ops::Add;

    type Fr =
        <ark_ec::short_weierstrass::Projective<ark_secp256k1::Config> as PrimeGroup>::ScalarField;

    pub fn prove_verify<G: CurveGroup>(
        crs: &CRS<G>,
        witness: &Witness<G, DensePolynomial<G::ScalarField>>,
        statement: &Statement<G>,
        rng: &mut OsRng,
    ) {
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
        verify(&mut verifier_state, crs, statement).expect("proof should verify");
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
            prove_verify(&crs, &witness1, &statement1, &mut rng);

            //can scale
            let alpha1 = Fr::rand(&mut rng);
            let alpha2 = Fr::rand(&mut rng);
            let witness = witness1.mul(alpha1).add(witness2.mul(alpha2));
            let statement = statement1.mul(alpha1).add(statement2.mul(alpha2));
            assert_eq!(statement, witness.statement(&crs, statement1.x), "statements are linear");
            prove_verify(&crs, &witness, &statement, &mut rng);


      }
    }
}
