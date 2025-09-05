use std::ops::Mul;

use ark_ec::CurveGroup;
use ark_ff::{Field, UniformRand, Zero};
use spongefish::{
    codecs::arkworks_algebra::{
        FieldDomainSeparator, FieldToUnitDeserialize, FieldToUnitSerialize, GroupDomainSeparator, GroupToUnitDeserialize, GroupToUnitSerialize, UnitToField
    }, DomainSeparator, ProofResult, ProverState, VerifierState
};

use crate::{
    circuit::utils::{mat_mul_l, mat_mul_r},
    ipa::{extended::{ExtendedBulletproofDomainSeparator, ExtendedStatement}, types as ipa_types, utils::dot},
    range::utils::{power_sequence, VectorPolynomial},
};

pub mod types;
pub(crate) mod utils;

pub trait CircuitProofDomainSeparator<G: CurveGroup> {
    fn circuit_proof_statement(self, n: usize) -> Self;
    fn add_circuit_proof(self, n: usize) -> Self;
}

impl<G> CircuitProofDomainSeparator<G> for DomainSeparator
where
    G: CurveGroup,
    Self: GroupDomainSeparator<G> + FieldDomainSeparator<G::ScalarField>,
{
    fn circuit_proof_statement(self, n: usize) -> Self {
        self.add_points(n, "circuit proof statement")
    }

    fn add_circuit_proof(mut self, n: usize) -> Self {
        self = self
            .add_points(3, "round-message: A_i, A_o, S")
            .challenge_scalars(2, "challenge [y,z]")
            .add_points(5, "round-message: T1, T3, T4, T5, T6")
            .challenge_scalars(1, "challenge x")
            .add_scalars(3, "round-message: tau_x, mu, t_hat")
            .add_extended_bulletproof(n);
        self
    }
}

pub fn prove<G: CurveGroup, Rng: rand::Rng>(
    prover_state: &mut ProverState,
    crs: &types::CRS<G>,
    circuit: &types::Circuit<G::ScalarField>,
    witness: &types::Witness<G::ScalarField>,
    rng: &mut Rng,
) -> ProofResult<Vec<u8>> {
    let n = crs.size();
    assert!(
        n == circuit.dim(),
        "CRS size and circuit dimension must match"
    );
    let [alpha, beta, rho]: [G::ScalarField; 3] =
        std::array::from_fn(|_| G::ScalarField::rand(rng));

    let a_i = crs.h.mul(alpha)
        + G::msm_unchecked(&crs.ipa_crs.gs, &witness.a_l)
        + G::msm_unchecked(&crs.ipa_crs.hs, &witness.a_r);

    let a_o = crs.h.mul(beta) + G::msm_unchecked(&crs.ipa_crs.gs, &witness.a_o);

    let s_l = (0..n)
        .map(|_| G::ScalarField::rand(rng))
        .collect::<Vec<_>>();
    let s_r = (0..n)
        .map(|_| G::ScalarField::rand(rng))
        .collect::<Vec<_>>();

    let s = crs.h.mul(rho)
        + G::msm_unchecked(&crs.ipa_crs.gs, &s_l)
        + G::msm_unchecked(&crs.ipa_crs.hs, &s_r);

    prover_state.add_points(&[a_i, a_o, s])?;
    let [y, z]: [G::ScalarField; 2] = prover_state.challenge_scalars()?;

    let y_vec = power_sequence(y, n);
    let y_inv_vec = power_sequence(y.inverse().expect("nonzero y"), n);
    let z_vec: Vec<G::ScalarField> = power_sequence(z, n).into_iter().map(|x| z * x).collect();

    let l_poly: VectorPolynomial<G::ScalarField> = {
        let v = mat_mul_l(&z_vec, &circuit.w_r);
        let coeffs = vec![
            vec![G::ScalarField::zero(); n],
            (0..n)
                .map(|i| witness.a_l[i] + (y_inv_vec[i] * v[i]))
                .collect(),
            witness.a_o.clone(),
            s_l,
        ];
        VectorPolynomial::new(coeffs, n)
    };
    let r_poly: VectorPolynomial<G::ScalarField> = {
        let v1 = mat_mul_l(&z_vec, &circuit.w_l);
        let v2 = mat_mul_l(&z_vec, &circuit.w_o);
        let coeffs = vec![
            (0..n).map(|i| v2[i] - y_inv_vec[i]).collect(),
            (0..n)
                .map(|i| (y_vec[i] * witness.a_r[i]) + v1[i])
                .collect(),
            vec![G::ScalarField::zero(); n],
            (0..n).map(|i| (y_vec[i] * s_r[i])).collect(),
        ];
        VectorPolynomial::new(coeffs, n)
    };

    let t_poly = l_poly.inner_product(&r_poly);

    // For some reason the paper treats index 2 (or 1 if 0-indexed) differently
    let taus: [Option<G::ScalarField>; 6] = std::array::from_fn(|i| {
        if i == 1 {
            None
        } else {
            Some(G::ScalarField::rand(rng))
        }
    });

    {
        let tts = taus
            .iter()
            .enumerate()
            .filter_map(|(i, tau_i_opt)| {
                tau_i_opt.map(|tau_i| crs.g.mul(t_poly[i]) + crs.h.mul(tau_i))
            })
            .collect::<Vec<_>>();
        prover_state.add_points(&tts)?;
    };

    {
        let [x]: [G::ScalarField; 1] = prover_state.challenge_scalars()?;

        let tao_x = {
            let init = x.pow([2]) * dot(&z_vec, &mat_mul_r(&circuit.w_v, &witness.gamma));
            taus.iter().enumerate().fold(init, |acc, (i, tau_i_opt)| {
                acc + tau_i_opt
                    .map(|tau_i| tau_i * x.pow(&[(i as u64) + 1]))
                    .unwrap_or(G::ScalarField::zero())
            })
        };

        let mu = alpha * x + beta * x.pow([2]) + rho * x.pow([3]);

        let l = l_poly.evaluate(x);
        let r = r_poly.evaluate(x);

        let witness = ipa_types::Witness::new(ipa_types::Vector(l), ipa_types::Vector(r));
        let hs_prime = create_hs_prime(&crs, y);

        let mut extended_statement: ExtendedStatement<G> =
            crate::ipa::extended::extended_statement(&crs.ipa_crs.gs, &hs_prime, &witness);

        extended_statement.p += crs.h.mul(-mu);

        prover_state.add_scalars(&[tao_x, mu, extended_statement.c])?;

        let crs = ipa_types::CRS {
            gs: crs.ipa_crs.gs.to_vec(),
            hs: hs_prime,
            u: crs.ipa_crs.u,
        };

        crate::ipa::extended::prove(prover_state, &crs, &extended_statement, &witness)?;
    }

    Ok(prover_state.narg_string().to_vec())
}

fn create_hs_prime<G: CurveGroup>(crs: &types::CRS<G>, y: G::ScalarField) -> Vec<G::Affine> {
    let y_inv_vec = power_sequence(y.inverse().expect("non-zero y"), crs.size());
    let hs = (0..y_inv_vec.len())
        .map(|i| crs.ipa_crs.hs[i].mul(y_inv_vec[i] * y))
        .collect::<Vec<_>>();
    G::normalize_batch(&hs)
}

pub fn verify<G: CurveGroup>(
    verifier_state: &mut VerifierState,
    crs: &types::CRS<G>,
    circuit: &types::Circuit<G::ScalarField>,
    vv: Vec<G::Affine>,
) -> ProofResult<()> {
    let n = crs.size();

    let [a_i, a_o, s]: [G; 3] = verifier_state.next_points()?;
    let [y, z]: [G::ScalarField; 2] = verifier_state.challenge_scalars()?;
    let tts: [Option<G>; 6] = {
        let [tau_1, tau_3, tau_4, tau_5, tau_6]: [G; 5] = verifier_state.next_points()?;
        [
            Some(tau_1),
            None,
            Some(tau_3),
            Some(tau_4),
            Some(tau_5),
            Some(tau_6),
        ]
    };
    let [x]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
    let [tao_x, mu, t_hat]: [G::ScalarField; 3] = verifier_state.next_scalars()?;

    let y_inv_vec = power_sequence(y.inverse().expect("nonzero y"), n);
    let z_vec: Vec<G::ScalarField> = power_sequence(z, n).into_iter().map(|x| z * x).collect();

    let delta_y_z = {
        let v = mat_mul_l(&z_vec, &circuit.w_r);
        let l: Vec<G::ScalarField> = (0..n).map(|i| (y_inv_vec[i] * v[i])).collect();
        let r = mat_mul_l(&z_vec, &circuit.w_l);
        dot(&l, &r)
    };

    {
        let lhs = crs.g.mul(t_hat) + crs.h.mul(tao_x);

        let rhs = crs
            .g
            .mul(x.square() * (delta_y_z + dot(&z_vec, &circuit.c)))
            + {
                let scalars = mat_mul_l(&z_vec, &circuit.w_v)
                    .iter()
                    .map(|zi| x.square() * zi)
                    .collect::<Vec<_>>();
                G::msm_unchecked(&vv, &scalars)
            }
            + {
                tts.iter()
                    .enumerate()
                    .filter_map(|(i, tau_i_opt)| {
                        tau_i_opt.map(|tau_i| tau_i.mul(x.pow(&[(i as u64) + 1])))
                    })
                    .fold(G::zero(), |acc, val| acc + val)
            };
            assert!((lhs - rhs).is_zero(), "Failed to verify t_hat = t(x)");
    };
    {

        let hs_prime: Vec<G::Affine> = create_hs_prime(crs, y);

        let ww_l = G::msm_unchecked(&hs_prime, &mat_mul_l(&z_vec, &circuit.w_l));
        let ww_r = {
            let v = mat_mul_l(&z_vec, &circuit.w_r);
            let scalars = (0..n).map(|i| y_inv_vec[i] * v[i]).collect::<Vec<_>>();
            G::msm_unchecked(&crs.ipa_crs.gs, &scalars)
        };
        let ww_o = G::msm_unchecked(&crs.ipa_crs.gs, &mat_mul_l(&z_vec, &circuit.w_o));

        let p: G = a_i.mul(x)
            + a_o.mul(x.square())
            + G::msm_unchecked(&hs_prime, &y_inv_vec)
            + ww_l.mul(x)
            + ww_r.mul(x)
            + ww_o
            + s.mul(x.pow([3]));



        let extended_statement = ExtendedStatement {
            p: p + crs.h.mul(-mu),
            c: t_hat,
        };

        let crs = ipa_types::CRS {
            gs: crs.ipa_crs.gs.to_vec(),
            hs: hs_prime,
            u: crs.ipa_crs.u,
        };
        crate::ipa::extended::verify(verifier_state, &crs, &extended_statement)

        }?;

    Ok(())
}
