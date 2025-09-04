use crate::ipa::extended::{ExtendedBulletproofDomainSeparator, ExtendedStatement};
use crate::ipa::utils::sum;
use crate::ipa::{self, types as ipa_types};
use crate::range::utils::{VectorPolynomial, bit_decomposition, create_hs_prime};
use crate::range::{types::CRS, utils::power_sequence};
use ark_ec::CurveGroup;
use ark_ff::{BigInteger, Field, One, PrimeField, UniformRand, Zero};
use spongefish::{
    DomainSeparator, ProofResult, ProverState,
    codecs::arkworks_algebra::{
        FieldDomainSeparator, FieldToUnitDeserialize, FieldToUnitSerialize, GroupDomainSeparator,
        GroupToUnitDeserialize, GroupToUnitSerialize, UnitToField,
    },
};
use std::ops::Mul;
use tracing::instrument;

#[allow(dead_code)]
pub trait AggregatedRangeProofDomainSeparator<G: CurveGroup> {
    fn aggregated_range_proof_statement(self, m: usize) -> Self;
    fn add_aggregated_range_proof(self, n_bits: usize, m: usize) -> Self;
}

impl<G> AggregatedRangeProofDomainSeparator<G> for DomainSeparator
where
    G: CurveGroup,
    Self: GroupDomainSeparator<G> + FieldDomainSeparator<G::ScalarField>,
{
    fn aggregated_range_proof_statement(self, m: usize) -> Self {
        self.add_points(m, "Range proof statement")
    }

    fn add_aggregated_range_proof(mut self, n_bits: usize, m: usize) -> Self {
        self = self
            .add_points(2, "round-message: A, S")
            .challenge_scalars(2, "challenge [y,z]")
            .add_points(2, "round-message: T1, T2")
            .challenge_scalars(1, "challenge x")
            .add_scalars(3, "round-message: t_x, mu, t_hat")
            .add_extended_bulletproof(n_bits * m);
        self
    }
}

pub struct Witness<Fr> {
    pub v: Vec<Fr>,
    pub gamma: Vec<Fr>,
    n_bits: usize,
}

impl<Fr: PrimeField> Witness<Fr> {
    pub fn new<Rng: rand::Rng>(v: Vec<Fr>, n_bits: usize, rang: &mut Rng) -> Self
    where
        Fr: PrimeField,
    {
        for val in &v {
            assert!(val.into_bigint().num_bits() as usize <= n_bits);
        }

        let gamma = (0..v.len()).map(|_| Fr::rand(rang)).collect();
        Witness { v, gamma, n_bits }
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.v.len()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Statement<G> {
    pub v: Vec<G>,
    n_bits: usize,
}

impl<G: CurveGroup> Statement<G> {
    pub fn new(crs: &CRS<G>, witness: &Witness<G::ScalarField>) -> Self {
        Statement {
            v: (0..witness.len())
                .map(|i| crs.g.mul(witness.v[i]) + crs.h.mul(witness.gamma[i]))
                .collect(),
            n_bits: witness.n_bits,
        }
    }
}

#[instrument(skip_all, fields(n_bits = witness.n_bits, m = witness.len()), level = "debug")]
pub fn prove<G: CurveGroup, Rng: rand::Rng>(
    mut prover_state: ProverState,
    crs: &CRS<G>,
    witness: &Witness<G::ScalarField>,
    rng: &mut Rng,
) -> ProofResult<Vec<u8>> {
    let n_bits = witness.n_bits;
    let m = witness.len();

    assert!(
        crs.size() >= n_bits * m,
        "CRS size is smaller than witness n_bits * m"
    );

    let gs = &crs.ipa_crs.gs[0..n_bits * m];
    let hs = &crs.ipa_crs.hs[0..n_bits * m];

    let two_vec = power_sequence(G::ScalarField::from(2u64), n_bits);

    let a_l: Vec<G::ScalarField> = {
        let mut res = Vec::with_capacity(n_bits * m);
        for val in &witness.v {
            let mut bits = bit_decomposition(*val);
            bits.resize(n_bits, G::ScalarField::zero());
            res.extend(bits);
        }
        assert!(res.len() == n_bits * m, "bad length");
        res
    };

    let a_r: Vec<G::ScalarField> = a_l.iter().map(|x| *x - G::ScalarField::one()).collect();

    let alpha: G::ScalarField = UniformRand::rand(rng);
    let a = crs.h.mul(alpha) + G::msm_unchecked(gs, &a_l) + G::msm_unchecked(hs, &a_r);
    let s_l: Vec<G::ScalarField> = (0..n_bits * m).map(|_| UniformRand::rand(rng)).collect();
    let s_r: Vec<G::ScalarField> = (0..n_bits * m).map(|_| UniformRand::rand(rng)).collect();

    let rho: G::ScalarField = UniformRand::rand(rng);
    let s = crs.h.mul(rho) + G::msm_unchecked(gs, &s_l) + G::msm_unchecked(hs, &s_r);
    prover_state.add_points(&[a, s])?;
    let [y, z]: [G::ScalarField; 2] = prover_state.challenge_scalars()?;

    let y_vec: Vec<G::ScalarField> = power_sequence(y, n_bits * m);

    let l_poly = {
        let coeffs = vec![
            (0..n_bits * m)
                .map(|i| a_l[i] - z * G::ScalarField::one())
                .collect(),
            s_l.clone(),
        ];
        VectorPolynomial::new(coeffs, n_bits * m)
    };

    let r_poly = {
        let sigma_sum = {
            let mut res = vec![G::ScalarField::zero(); n_bits * m];
            let mut z_power = z; // z^1
            for j in 0..m {
                z_power *= z; // z^{1+j+1} = z^{2+j}
                for i in 0..n_bits {
                    res[j * n_bits + i] = two_vec[i] * z_power;
                }
            }
            res
        };
        let coeffs = vec![
            (0..n_bits * m)
                .map(|i| (y_vec[i] * (a_r[i] + z * G::ScalarField::one())) + sigma_sum[i])
                .collect(),
            (0..n_bits * m).map(|i| y_vec[i] * s_r[i]).collect(),
        ];
        VectorPolynomial::new(coeffs, n_bits * m)
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

        let tao_x = {
            let sigma_summand = {
                let mut sum = G::ScalarField::zero();
                let mut z_power = z; // z^1
                for j in 0..m {
                    z_power *= z; // z^{1+j+1} = z^{2+j}
                    sum += z_power * witness.gamma[j];
                }
                sum
            };
            tao1 * x + tao2 * x.square() + sigma_summand
        };
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

        ipa::extended::prove(&mut prover_state, &crs, &extended_statement, &witness)
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
    let m = statement.v.len();

    let [a, s]: [G; 2] = verifier_state.next_points()?;
    let [y, z]: [G::ScalarField; 2] = verifier_state.challenge_scalars()?;
    let [tt1, tt2]: [G; 2] = verifier_state.next_points()?;
    let [x]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
    let [tao_x, mu, t_hat]: [G::ScalarField; 3] = verifier_state.next_scalars()?;

    let two_vec = power_sequence(G::ScalarField::from(2u64), n_bits);
    let y_vec: Vec<G::ScalarField> = power_sequence(y, n_bits * m);

    {
        let tt1 = tt1.into_affine();
        let tt2 = tt2.into_affine();

        let lhs = crs.g.mul(t_hat) + crs.h.mul(tao_x);
        let rhs = {
            let sigma_summand: G::ScalarField = {
                let d = sum(&two_vec);
                let mut sum = G::ScalarField::zero();
                let mut z_power = z * z; // z^2
                for _j in 0..m {
                    z_power *= z; // z^{2+j+1} = z^{3+j} (for j=0 this gives z^3, for j=1 this gives z^4, etc.)
                    sum += z_power * d;
                }
                sum
            };

            let delta_y_z = { (z - z.square()) * sum(&y_vec) - sigma_summand };

            let z_vec = {
                let mut powers = power_sequence(z, m);
                powers.iter_mut().for_each(|x| *x *= z.square());
                powers
            };
            let vs = G::normalize_batch(&statement.v);

            crs.g.mul(delta_y_z) + G::msm_unchecked(&vs, &z_vec) + tt1.mul(x) + tt2.mul(x.square())
        };
        assert!(
            (lhs - rhs).is_zero(),
            "Failed to verify t_hat = t(x) = t_0 + t_1 x + t_2 x^2"
        );
    };

    {
        let gs = &crs.ipa_crs.gs[0..n_bits * m];
        let hs_prime = create_hs_prime(crs, y_vec.clone());

        let p: G = {
            // Optimization: Batch all hs_prime operations into a single MSM
            // Combine pi_sum and hs_scalars computations
            let mut hs_combined_scalars = vec![G::ScalarField::zero(); n_bits * m];

            // First, set base hs_scalars: z * y_vec[i]
            for i in 0..n_bits * m {
                hs_combined_scalars[i] = z * y_vec[i];
            }

            // Then, add pi_sum contribution: two_vec[i] * z^{2+j} for each segment j
            let mut z_power = z; // z^1
            for j in 0..m {
                z_power *= z; // z^{2+j}
                for i in 0..n_bits {
                    hs_combined_scalars[j * n_bits + i] += two_vec[i] * z_power;
                }
            }

            // Pre-allocate gs_scalars to avoid vec! allocation
            let mut gs_scalars = Vec::with_capacity(n_bits * m);
            gs_scalars.resize(n_bits * m, -z);

            a + s.mul(x)
                + G::msm_unchecked(gs, &gs_scalars)
                + G::msm_unchecked(&hs_prime, &hs_combined_scalars)
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
        ipa::extended::verify(verifier_state, &crs, &extended_statement)
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
        fn test_aggregated_range_proof(
            n_bits in prop_oneof![Just(64)],
            m in prop_oneof![Just(2usize), Just(4), Just(8), Just(16), Just(32), Just(64), Just(128), Just(256), Just(512)]
        ) {

            let mut rng = OsRng;
            let crs: CRS<Projective> = CRS::rand(n_bits * m);

            // Generate m random values in range [0, 2^n_bits)
            let max_value = (1u128 << n_bits.min(127)) - 1;
            let v: Vec<Fr> = (0..m)
                .map(|_| Fr::from(rand::Rng::gen_range(&mut rng, 0u128..=max_value)))
                .collect();

            let witness = Witness::<Fr>::new(v, n_bits, &mut rng);

            let statement = Statement::new(&crs, &witness);

            let domain_separator = {
                let domain_separator = DomainSeparator::new("test-range-proof");
                // add the IO of the bulletproof statement
                let domain_separator =
                    AggregatedRangeProofDomainSeparator::<Projective>::aggregated_range_proof_statement(domain_separator, m)
                        .ratchet();
                // add the IO of the bulletproof protocol (the transcript)
                AggregatedRangeProofDomainSeparator::<Projective>::add_aggregated_range_proof(domain_separator, n_bits, m)
            };

            let mut prover_state = domain_separator.to_prover_state();


            prover_state.public_points(&statement.v).unwrap();
            prover_state.ratchet().unwrap();

            let proof = prove(prover_state, &crs, &witness, &mut rng).unwrap();

            tracing::info!("proof size: {} bytes", proof.len());

            let mut verifier_state = domain_separator.to_verifier_state(&proof);
            verifier_state
                .public_points(&statement.v)
                .expect("cannot add statment");
            verifier_state.ratchet().expect("failed to ratchet");
            verify(verifier_state, &crs, &statement).expect("proof should verify")
        }
    }
}
