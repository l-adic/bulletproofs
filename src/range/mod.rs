pub mod aggregate;
pub mod types;
pub(crate) mod utils;

use ark_ec::{CurveGroup, PrimeGroup};
use ark_ff::{Field, One, UniformRand, Zero};
use spongefish::{
    Codec, Encoding, NargDeserialize, ProverState, VerificationError, VerificationResult,
};
use std::{iter::successors, ops::Mul};
use tracing::instrument;

use crate::{
    ipa::{
        extended::{self},
        types::{self as ipa_types},
    },
    msm::Msm,
    range::{
        types::{CRS, Statement, VectorPolynomial, Witness},
        utils::{bit_decomposition, create_hs_prime},
    },
    vector_ops::{VectorOps, sum},
};

// pub trait RangeProofDomainSeparator<G: CurveGroup> {
//     fn range_proof_statement(self) -> Self;
//     fn add_range_proof(self, n: usize) -> Self;
// }

// impl<G> RangeProofDomainSeparator<G> for DomainSeparator
// where
//     G: CurveGroup,
//     Self: GroupDomainSeparator<G> + FieldDomainSeparator<G::ScalarField>,
// {
//     fn range_proof_statement(self) -> Self {
//         self.add_points(1, "Range proof statement")
//     }

//     fn add_range_proof(mut self, n: usize) -> Self {
//         self = self
//             .add_points(2, "round-message: A, S")
//             .challenge_scalars(2, "challenge [y,z]")
//             .add_points(2, "round-message: T1, T2")
//             .challenge_scalars(1, "challenge x")
//             .add_scalars(3, "round-message: t_x, mu, t_hat")
//             .add_extended_bulletproof(n);
//         self
//     }
// }

#[instrument(skip_all, fields(nbits = witness.n_bits), level = "debug")]
pub fn prove<G: CurveGroup + Encoding, Rng: rand::Rng>(
    mut prover_state: ProverState,
    crs: &CRS<G>,
    witness: &Witness<G::ScalarField>,
    rng: &mut Rng,
) -> Vec<u8>
where
    <G as PrimeGroup>::ScalarField: Codec,
{
    let n_bits = witness.n_bits;
    assert!(
        crs.size() >= n_bits,
        "CRS size is smaller than witness nbits"
    );

    let gs = &crs.ipa_crs.gs[0..n_bits];
    let hs = &crs.ipa_crs.hs[0..n_bits];

    let one_vec: Vec<G::ScalarField> = vec![G::ScalarField::one(); n_bits];
    // powers of 2
    let two_vec: Vec<G::ScalarField> = successors(Some(G::ScalarField::one()), |succ| {
        Some(*succ * G::ScalarField::from(2u64))
    })
    .take(n_bits)
    .collect();

    let a_l: Vec<G::ScalarField> = {
        let mut bits = bit_decomposition(witness.v);
        bits.resize(n_bits, G::ScalarField::zero());
        bits
    };

    let a_r: Vec<G::ScalarField> = a_l.iter().map(|x| *x - G::ScalarField::one()).collect();

    let alpha: G::ScalarField = UniformRand::rand(rng);
    let rho: G::ScalarField = UniformRand::rand(rng);
    let s_l = (0..n_bits)
        .map(|_| UniformRand::rand(rng))
        .collect::<Vec<_>>();
    let s_r = (0..n_bits)
        .map(|_| UniformRand::rand(rng))
        .collect::<Vec<_>>();

    let (a, s) = {
        let bases: Vec<G::Affine> = gs.iter().cloned().chain(hs.iter().cloned()).collect();
        let a_scalars: Vec<G::ScalarField> =
            a_l.iter().cloned().chain(a_r.iter().cloned()).collect();
        let s_scalars: Vec<G::ScalarField> =
            s_l.iter().copied().chain(s_r.iter().copied()).collect();

        rayon::join(
            || crs.h.mul(alpha) + G::msm_unchecked(&bases, &a_scalars),
            || crs.h.mul(rho) + G::msm_unchecked(&bases, &s_scalars),
        )
    };
    prover_state.prover_messages(&[a, s]);
    let [y, z]: [G::ScalarField; 2] = [
        prover_state.verifier_message(),
        prover_state.verifier_message(),
    ];
    let y_vec: Vec<G::ScalarField> =
        successors(Some(G::ScalarField::one()), |succ| Some(*succ * y))
            .take(n_bits)
            .collect();

    let l_poly = {
        let coeffs = vec![
            a_l.into_iter()
                .vector_sub(one_vec.iter().copied().scale(z))
                .collect(),
            s_l,
        ];
        VectorPolynomial::new(coeffs, n_bits)
    };

    let r_poly = {
        let coeffs = vec![
            y_vec
                .iter()
                .copied()
                .hadamard(
                    a_r.iter()
                        .copied()
                        .vector_add(one_vec.iter().copied().scale(z)),
                )
                .vector_add(two_vec.iter().copied().scale(z.square()))
                .collect(),
            y_vec.iter().copied().hadamard(s_r).collect(),
        ];
        VectorPolynomial::new(coeffs, n_bits)
    };

    let tao1: G::ScalarField = UniformRand::rand(rng);
    let tao2: G::ScalarField = UniformRand::rand(rng);

    {
        let t_poly = l_poly.inner_product(&r_poly);
        let tt1 = crs.g.mul(t_poly[1]) + crs.h.mul(tao1);
        let tt2 = crs.g.mul(t_poly[2]) + crs.h.mul(tao2);

        prover_state.prover_messages(&[tt1, tt2]);
    }

    {
        let x: G::ScalarField = prover_state.verifier_message();

        let tao_x = tao2 * x.square() + tao1 * x + z.square() * witness.gamma;
        let mu = alpha + rho * x;
        let l: Vec<G::ScalarField> = l_poly.evaluate(x);
        let r: Vec<G::ScalarField> = r_poly.evaluate(x);

        let witness = ipa_types::Witness::new(l, r);

        let hs_prime = G::normalize_batch(
            &create_hs_prime::<G>(hs, y)
                .into_iter()
                .map(|(h, y_inv_i)| h.mul(y_inv_i))
                .collect::<Vec<_>>(),
        );

        let mut extended_statement: ipa_types::extended::Statement<G> =
            witness.extended_statement(&crs.ipa_crs);

        extended_statement.p += crs.h.mul(-mu);

        prover_state.prover_messages(&[tao_x, mu, extended_statement.c]);
        let crs = ipa_types::CRS {
            gs: gs.to_vec(),
            hs: hs_prime,
            u: crs.ipa_crs.u,
        };

        extended::prove(&mut prover_state, &crs, &extended_statement, &witness);
    }

    prover_state.narg_string().to_vec()
}

#[instrument(skip_all, fields(nbits = statement.n_bits), level = "debug")]
pub fn verify_aux<G: CurveGroup + Encoding + NargDeserialize, Rng: rand::Rng>(
    verifier_state: &mut spongefish::VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
    rng: &mut Rng,
) -> VerificationResult<Msm<G>>
where
    <G as PrimeGroup>::ScalarField: Codec,
{
    let n_bits = statement.n_bits;
    let [a, s]: [G; 2] = verifier_state.prover_messages()?;
    let [y, z]: [G::ScalarField; 2] = [
        verifier_state.verifier_message(),
        verifier_state.verifier_message(),
    ];
    let [tt1, tt2]: [G; 2] = verifier_state.prover_messages()?;
    let x: G::ScalarField = verifier_state.verifier_message();
    let [tao_x, mu, t_hat]: [G::ScalarField; 3] = verifier_state.prover_messages()?;

    let two_vec: Vec<G::ScalarField> = successors(Some(G::ScalarField::one()), |succ| {
        Some(*succ * G::ScalarField::from(2u64))
    })
    .take(n_bits)
    .collect();

    let y_vec: Vec<G::ScalarField> =
        successors(Some(G::ScalarField::one()), |succ| Some(*succ * y))
            .take(n_bits)
            .collect();

    let (g, msm) = rayon::join(
        || {
            let tt1 = tt1.into_affine();
            let tt2 = tt2.into_affine();

            let delta_y_z = {
                let z_cubed = z * z.square();
                (z - z.square()) * sum(y_vec.iter().copied())
                    - z_cubed * sum(two_vec.iter().copied())
            };
            crs.g.mul(t_hat - delta_y_z) + crs.h.mul(tao_x)
                - (statement.v.mul(z.square()) + tt1.mul(x) + tt2.mul(x.square()))
        },
        || {
            let gs = &crs.ipa_crs.gs[0..n_bits];
            let hs = &crs.ipa_crs.hs[0..n_bits];
            let scaled_hs = create_hs_prime::<G>(hs, y);
            let hs_prime = G::normalize_batch(
                &scaled_hs
                    .iter()
                    .map(|(h, y_inv_i)| h.mul(y_inv_i))
                    .collect::<Vec<_>>(),
            );

            let p: G = {
                a + s.mul(x) + {
                    let bases: Vec<G::Affine> = gs.iter().chain(hs_prime.iter()).copied().collect();
                    let scalars: Vec<G::ScalarField> = {
                        let neg_z = std::iter::repeat_n(-z, n_bits);
                        let hs_scalars = y_vec
                            .iter()
                            .copied()
                            .scale(z)
                            .vector_add(two_vec.iter().copied().scale(z.square()));
                        neg_z.chain(hs_scalars).collect()
                    };
                    G::msm_unchecked(&bases, &scalars)
                }
            };

            let extended_statement = ipa_types::extended::Statement {
                p: p + crs.h.mul(-mu),
                c: t_hat,
                witness_size: n_bits as u64,
            };

            let mut msm = extended::verify_aux(verifier_state, &crs.ipa_crs, &extended_statement)?;
            msm.scale_elems(scaled_hs.into_iter());
            Ok::<_, VerificationError>(msm)
        },
    );
    let mut msm = msm?;

    let alpha = G::ScalarField::rand(rng);
    msm.upsert(g.into_affine(), alpha);

    Ok(msm)
}

#[instrument(skip_all, fields(nbits = statement.n_bits), level = "debug")]
pub fn verify<G: CurveGroup + Encoding + NargDeserialize, Rng: rand::Rng>(
    verifier_state: &mut spongefish::VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
    rng: &mut Rng,
) -> VerificationResult<()>
where
    <G as PrimeGroup>::ScalarField: Codec,
{
    let msm = verify_aux(verifier_state, crs, statement, rng)?;
    let g = msm.execute();
    if g.is_zero() {
        Ok(())
    } else {
        Err(VerificationError)
    }
}

// #[cfg(test)]
// mod tests_range {
// Tests commented out - need to be updated for new spongefish API
