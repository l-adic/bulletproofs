pub mod aggregate;
pub mod types;
pub(crate) mod utils;

use crate::{
    ipa::{
        self,
        extended::{self, ExtendedBulletproofDomainSeparator, ExtendedStatement},
        types as ipa_types,
        utils::sum,
    },
    range::{
        types::{CRS, Statement, Witness},
        utils::{VectorPolynomial, bit_decomposition, create_hs_prime, power_sequence},
    },
};
use ark_ec::CurveGroup;
use ark_ff::{Field, One, UniformRand, Zero};
use spongefish::{
    DomainSeparator, ProofResult, ProverState,
    codecs::arkworks_algebra::{
        FieldDomainSeparator, FieldToUnitDeserialize, FieldToUnitSerialize, GroupDomainSeparator,
        GroupToUnitDeserialize, GroupToUnitSerialize, UnitToField,
    },
};
use std::ops::Mul;
use tracing::instrument;

pub trait RangeProofDomainSeparator<G: CurveGroup> {
    fn range_proof_statement(self) -> Self;
    fn add_range_proof(self, n: usize) -> Self;
}

impl<G> RangeProofDomainSeparator<G> for DomainSeparator
where
    G: CurveGroup,
    Self: GroupDomainSeparator<G> + FieldDomainSeparator<G::ScalarField>,
{
    fn range_proof_statement(self) -> Self {
        self.add_points(1, "Range proof statement")
    }

    fn add_range_proof(mut self, n: usize) -> Self {
        self = self
            .add_points(2, "round-message: A, S")
            .challenge_scalars(2, "challenge [y,z]")
            .add_points(2, "round-message: T1, T2")
            .challenge_scalars(1, "challenge x")
            .add_scalars(3, "round-message: t_x, mu, t_hat")
            .add_extended_bulletproof(n);
        self
    }
}

#[instrument(skip_all, fields(nbits = witness.n_bits), level = "debug")]
pub fn prove<G: CurveGroup, Rng: rand::Rng>(
    mut prover_state: ProverState,
    crs: &CRS<G>,
    witness: &Witness<G::ScalarField>,
    rng: &mut Rng,
) -> ProofResult<Vec<u8>> {
    let n_bits = witness.n_bits;
    assert!(
        crs.size() >= n_bits,
        "CRS size is smaller than witness nbits"
    );

    let gs = &crs.ipa_crs.gs[0..n_bits];
    let hs = &crs.ipa_crs.hs[0..n_bits];

    // powers of 2
    let two_vec: Vec<G::ScalarField> = power_sequence(G::ScalarField::from(2u64), n_bits);

    let a_l: Vec<G::ScalarField> = {
        let mut bits = bit_decomposition(witness.v);
        bits.resize(n_bits, G::ScalarField::zero());
        bits
    };

    let a_r: Vec<G::ScalarField> = a_l.iter().map(|x| *x - G::ScalarField::one()).collect();

    let alpha: G::ScalarField = UniformRand::rand(rng);
    let a = crs.h.mul(alpha) + G::msm_unchecked(gs, &a_l) + G::msm_unchecked(hs, &a_r);
    let s_l: Vec<G::ScalarField> = (0..n_bits).map(|_| UniformRand::rand(rng)).collect();
    let s_r: Vec<G::ScalarField> = (0..n_bits).map(|_| UniformRand::rand(rng)).collect();

    let rho: G::ScalarField = UniformRand::rand(rng);
    let s = crs.h.mul(rho) + G::msm_unchecked(gs, &s_l) + G::msm_unchecked(hs, &s_r);
    prover_state.add_points(&[a, s])?;
    let [y, z]: [G::ScalarField; 2] = prover_state.challenge_scalars()?;
    let y_vec: Vec<G::ScalarField> = power_sequence(y, n_bits);

    let l_poly = {
        let coeffs = vec![
            (0..n_bits)
                .map(|i| a_l[i] - G::ScalarField::one() * z)
                .collect(),
            s_l.clone(),
        ];
        VectorPolynomial::new(coeffs, n_bits)
    };

    let r_poly = {
        let coeffs = vec![
            (0..n_bits)
                .map(|i| {
                    (y_vec[i] * (a_r[i] + G::ScalarField::one() * z)) + two_vec[i] * z.square()
                })
                .collect(),
            (0..n_bits).map(|i| y_vec[i] * s_r[i]).collect(),
        ];
        VectorPolynomial::new(coeffs, n_bits)
    };

    let tao1: G::ScalarField = UniformRand::rand(rng);
    let tao2: G::ScalarField = UniformRand::rand(rng);

    {
        let t_poly = l_poly.inner_product(&r_poly);
        let tt1 = crs.g.mul(t_poly[1]) + crs.h.mul(tao1);
        let tt2 = crs.g.mul(t_poly[2]) + crs.h.mul(tao2);

        prover_state.add_points(&[tt1, tt2])?;
    }

    {
        let [x]: [G::ScalarField; 1] = prover_state.challenge_scalars()?;

        let tao_x = tao2 * x.square() + tao1 * x + z.square() * witness.gamma;
        let mu = alpha + rho * x;
        let l: Vec<G::ScalarField> = l_poly.evaluate(x);
        let r: Vec<G::ScalarField> = r_poly.evaluate(x);

        let witness = ipa_types::Witness::new(ipa_types::Vector(l), ipa_types::Vector(r));

        let hs_prime = create_hs_prime(crs, y_vec);

        let mut extended_statement: ExtendedStatement<G> =
            ipa::extended::extended_statement(gs, &hs_prime, &witness);

        extended_statement.p += crs.h.mul(-mu);

        prover_state.add_scalars(&[tao_x, mu, extended_statement.c])?;
        let crs = ipa_types::CRS {
            gs: gs.to_vec(),
            hs: hs_prime,
            u: crs.ipa_crs.u,
        };

        extended::prove(&mut prover_state, &crs, &extended_statement, &witness)
    }?;

    Ok(prover_state.narg_string().to_vec())
}

#[instrument(skip_all, fields(nbits = statement.n_bits), level = "debug")]
pub fn verify<G: CurveGroup>(
    mut verifier_state: spongefish::VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
) -> ProofResult<()> {
    let n_bits = statement.n_bits;
    let [a, s]: [G; 2] = verifier_state.next_points()?;
    let [y, z]: [G::ScalarField; 2] = verifier_state.challenge_scalars()?;
    let [tt1, tt2]: [G; 2] = verifier_state.next_points()?;
    let [x]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
    let [tao_x, mu, t_hat]: [G::ScalarField; 3] = verifier_state.next_scalars()?;

    let two_vec: Vec<G::ScalarField> = power_sequence(G::ScalarField::from(2u64), n_bits);
    let y_vec: Vec<G::ScalarField> = power_sequence(y, n_bits);

    {
        let tt1 = tt1.into_affine();
        let tt2 = tt2.into_affine();

        let lhs = crs.g.mul(t_hat) + crs.h.mul(tao_x);
        let rhs = {
            let delta_y_z = {
                let z_cubed = z * z.square();
                (z - z.square()) * sum(&y_vec) - z_cubed * sum(&two_vec)
            };

            statement.v.mul(z.square()) + crs.g.mul(delta_y_z) + tt1.mul(x) + tt2.mul(x.square())
        };
        assert!(
            (lhs - rhs).is_zero(),
            "Failed to verify t_hat = t(x) = t_0 + t_1 x + t_2 x^2"
        );
    };

    {
        let gs = &crs.ipa_crs.gs[0..n_bits];
        let hs_prime = create_hs_prime(crs, y_vec.clone());

        let p: G = {
            let hs_scalars: Vec<G::ScalarField> = (0..n_bits)
                .map(|i| (z * y_vec[i]) + z.square() * two_vec[i])
                .collect();
            let neg_z: Vec<G::ScalarField> = vec![-z; n_bits];
            a + s.mul(x) + G::msm_unchecked(gs, &neg_z) + G::msm_unchecked(&hs_prime, &hs_scalars)
        };

        let extended_statement = ExtendedStatement {
            p: p + crs.h.mul(-mu),
            c: t_hat,
        };

        let crs = ipa_types::CRS {
            gs: gs.to_vec(),
            hs: hs_prime,
            u: crs.ipa_crs.u,
        };
        extended::verify(verifier_state, &crs, &extended_statement)
    }?;

    Ok(())
}

#[cfg(test)]
mod tests_range {
    use super::*;
    use ark_secp256k1::{Fr, Projective};
    use proptest::{prelude::*, test_runner::Config};
    use rand::rngs::OsRng;
    use spongefish::codecs::arkworks_algebra::CommonGroupToUnit;

    proptest! {
          #![proptest_config(Config::with_cases(10))]
          #[test]
        fn test_range_proof(n in prop_oneof![Just(2usize), Just(4), Just(8), Just(16), Just(32), Just(64)]) {

            let mut rng = OsRng;
            let crs: CRS<Projective> = CRS::rand(n);
            // pick a random Fr value in the range [0, 2^n) via bigint conversion
            let max_value = (1u128 << n) - 1;
            let v = Fr::from(rand::Rng::gen_range(&mut rng, 0u128..=max_value));
            let witness = Witness::<Fr>::new(v, n, &mut rng);

            let domain_separator = {
                let domain_separator = DomainSeparator::new("test-range-proof");
                // add the IO of the bulletproof statement
                let domain_separator =
                    RangeProofDomainSeparator::<Projective>::range_proof_statement(domain_separator)
                        .ratchet();
                // add the IO of the bulletproof protocol (the transcript)
                RangeProofDomainSeparator::<Projective>::add_range_proof(domain_separator, n)
            };

            let mut prover_state = domain_separator.to_prover_state();

            let statement = Statement::new(&crs, &witness);

            prover_state.public_points(&[statement.v]).unwrap();
            prover_state.ratchet().unwrap();

            let proof = prove(prover_state, &crs, &witness, &mut rng).unwrap();

            tracing::info!("proof size: {} bytes", proof.len());

            let mut verifier_state = domain_separator.to_verifier_state(&proof);
            verifier_state
                .public_points(&[statement.v])
                .expect("cannot add statment");
            verifier_state.ratchet().expect("failed to ratchet");
            verify(verifier_state, &crs, &statement).expect("proof should verify")
        }
    }
}
