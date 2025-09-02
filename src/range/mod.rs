pub mod types;
pub(crate) mod utils;

use crate::{
    ipa::utils::dot,
    range::{
        types::{CRS, Statement, Witness},
        utils::{VectorPolynomial, bit_decomposition},
    },
};
use ark_ec::CurveGroup;
use ark_ff::{Field, One, UniformRand, Zero};
use spongefish::codecs::arkworks_algebra::FieldToUnitDeserialize;
use spongefish::codecs::arkworks_algebra::FieldToUnitSerialize;
use spongefish::codecs::arkworks_algebra::GroupToUnitDeserialize;
use spongefish::codecs::arkworks_algebra::UnitToField;
use spongefish::{
    DomainSeparator, ProofResult, ProverState,
    codecs::arkworks_algebra::{FieldDomainSeparator, GroupDomainSeparator, GroupToUnitSerialize},
};
use std::array;
use std::ops::Mul;

pub trait RangeProofDomainSeparator<G: CurveGroup> {
    fn range_proof_statement(self) -> Self;
    fn add_range_proof(self, n: usize) -> Self;
}

impl<G> RangeProofDomainSeparator<G> for DomainSeparator
where
    G: CurveGroup,
    Self: GroupDomainSeparator<G> + FieldDomainSeparator<G::ScalarField>,
{
    /// The IO of the range proof statement
    fn range_proof_statement(self) -> Self {
        self.add_points(1, "Range proof statement")
    }

    /// The IO of the range proof protocol
    fn add_range_proof(mut self, n: usize) -> Self {
        self = self
            .add_points(2, "round-message: A, S")
            .challenge_scalars(2, "challenge [y,z]")
            .add_points(2, "round-message: T1, T2")
            .challenge_scalars(1, "challenge x")
            .add_scalars(3, "round-message: t_x, mu, t_hat")
            .add_scalars(n, "round-message: l")
            .add_scalars(n, "round-message: r");
        self
    }
}

pub fn prove<G: CurveGroup, Rng: rand::Rng, const N: usize>(
    mut prover_state: ProverState,
    crs: &CRS<G>,
    _statement: &Statement<N, G>,
    witness: &Witness<N, G::ScalarField>,
    rng: &mut Rng,
) -> ProofResult<Vec<u8>> {
    assert!(crs.size() >= N, "CRS size is smaller than witness nbits");

    let one_vec: [G::ScalarField; N] = [G::ScalarField::one(); N];
    let two_vec: [G::ScalarField; N] =
        array::from_fn(|i| G::ScalarField::from(2u64).pow([i as u64]));

    let a_l: [G::ScalarField; N] = {
        let mut bits = bit_decomposition(witness.v);
        bits.resize(N, G::ScalarField::zero());
        bits.try_into().unwrap()
    };

    let a_r: [G::ScalarField; N] = a_l.map(|x| x - G::ScalarField::one());

    let alpha: G::ScalarField = UniformRand::rand(rng);
    let a = crs.h.mul(alpha)
        + G::msm_unchecked(&crs.gs[0..N], &a_l)
        + G::msm_unchecked(&crs.hs[0..N], &a_r);
    let s_l: [G::ScalarField; N] = array::from_fn(|_| UniformRand::rand(rng));
    let s_r: [G::ScalarField; N] = array::from_fn(|_| UniformRand::rand(rng));

    let rho: G::ScalarField = UniformRand::rand(rng);
    let s = crs.h.mul(rho)
        + G::msm_unchecked(&crs.gs[0..N], &s_l)
        + G::msm_unchecked(&crs.hs[0..N], &s_r);
    prover_state.add_points(&[a, s])?;
    let [y, z]: [G::ScalarField; 2] = prover_state.challenge_scalars()?;
    let y_vec: [G::ScalarField; N] = array::from_fn(|i| y.pow([i as u64]));

    let l_poly = {
        let coeffs = vec![array::from_fn(|i| a_l[i] - one_vec[i] * z), s_l];
        VectorPolynomial { coeffs }
    };

    let r_poly = {
        let coeffs = vec![
            array::from_fn(|i| (y_vec[i] * (a_r[i] + one_vec[i] * z)) + two_vec[i] * z.square()),
            array::from_fn(|i| y_vec[i] * s_r[i]),
        ];
        VectorPolynomial { coeffs }
    };

    let t_poly = l_poly.inner_product(&r_poly);

    let tao1: G::ScalarField = UniformRand::rand(rng);
    let tao2: G::ScalarField = UniformRand::rand(rng);

    let tt1 = crs.g.mul(t_poly[1]) + crs.h.mul(tao1);
    let tt2 = crs.g.mul(t_poly[2]) + crs.h.mul(tao2);

    prover_state.add_points(&[tt1, tt2])?;

    let [x]: [G::ScalarField; 1] = prover_state.challenge_scalars()?;

    let l: [G::ScalarField; N] = l_poly.evaluate(x);
    let r: [G::ScalarField; N] = r_poly.evaluate(x);
    let t_hat = dot(&l, &r);

    let tao_x = tao2 * x.square() + tao1 * x + z.square() * witness.gamma;
    let mu = alpha + rho * x;

    prover_state.add_scalars(&[tao_x, mu, t_hat])?;
    prover_state.add_scalars(&l)?;
    prover_state.add_scalars(&r)?;

    Ok(prover_state.narg_string().to_vec())
}

pub fn verify<G: CurveGroup, const N: usize>(
    mut verifier_state: spongefish::VerifierState,
    crs: &CRS<G>,
    statement: &Statement<N, G>,
) -> ProofResult<()> {
    let [a, s]: [G; 2] = verifier_state.next_points()?;
    let [y, z]: [G::ScalarField; 2] = verifier_state.challenge_scalars()?;
    let [tt1, tt2]: [G; 2] = verifier_state.next_points()?;
    let [x]: [G::ScalarField; 1] = verifier_state.challenge_scalars()?;
    let [tao_x, mu, t_hat]: [G::ScalarField; 3] = verifier_state.next_scalars()?;
    let l: [G::ScalarField; N] = verifier_state.next_scalars()?;
    let r: [G::ScalarField; N] = verifier_state.next_scalars()?;

    let one_vec = [G::ScalarField::one(); N];
    let two_vec: [G::ScalarField; N] =
        array::from_fn(|i| G::ScalarField::from(2u64).pow([i as u64]));
    let y_vec: [G::ScalarField; N] = array::from_fn(|i| y.pow([i as u64]));

    let delta_y_z = {
        let z_cubed = z * z.square();
        (z - z.square()) * dot(&one_vec, &y_vec) - z_cubed * dot(&one_vec, &two_vec)
    };
    let hs: Vec<G::Affine> = {
        let hs: [G; N] = array::from_fn(|i| crs.hs[i].mul(y.inverse().unwrap().pow([i as u64])));
        G::normalize_batch(&hs)
    };

    {
        let tt1 = tt1.into_affine();
        let tt2 = tt2.into_affine();
        let lhs = crs.g.mul(t_hat) + crs.h.mul(tao_x);
        let rhs =
            statement.v.mul(z.square()) + crs.g.mul(delta_y_z) + tt1.mul(x) + tt2.mul(x.square());
        assert!(
            (lhs - rhs).is_zero(),
            "Failed to verify t_hat = t(x) = t_0 + t_1 x + t_2 x^2"
        );
    };

    {
        let p: G = {
            let hs_exp: [G::ScalarField; N] =
                array::from_fn(|i| (z * y_vec[i]) + z.square() * two_vec[i]);
            let minus_z_times_one_vec = one_vec.map(|x| -z * x);
            a + s.mul(x)
                + G::msm_unchecked(&crs.gs[0..N], &minus_z_times_one_vec)
                + G::msm_unchecked(&hs, &hs_exp)
        };

        let rhs = crs.h.mul(mu) + G::msm_unchecked(&crs.gs[0..N], &l) + G::msm_unchecked(&hs, &r);

        assert!(
            (p - rhs).is_zero(),
            "Failed to verify inner product relation, i.e. p {p:?} != rhs {rhs:?}"
        );
    };

    {
        assert!(t_hat == dot(&l, &r), "t_hat does not equal <l,r>");
    }

    Ok(())
}

#[cfg(test)]
mod tests_range {
    use super::*;
    use ark_secp256k1::{Fr, Projective};
    use ark_std::UniformRand;
    use rand::rngs::OsRng;
    use spongefish::codecs::arkworks_algebra::CommonGroupToUnit;

    // test that we can construct a range proof for N = 16
    #[test]
    fn test_range_proof() {
        let n = 16;
        let mut rng = OsRng;
        let crs: CRS<Projective> = CRS {
            gs: (0..n)
                .map(|_| Projective::rand(&mut rng).into_affine())
                .collect(),
            hs: (0..n)
                .map(|_| Projective::rand(&mut rng).into_affine())
                .collect(),
            g: Projective::rand(&mut rng).into_affine(),
            h: Projective::rand(&mut rng).into_affine(),
        };
        let v = Fr::from(1234u64);
        let witness = Witness::<16, Fr>::new(v, &mut rng);

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

        let proof = prove(prover_state, &crs, &statement, &witness, &mut rng).unwrap();

        let mut verifier_state = domain_separator.to_verifier_state(&proof);
        verifier_state
            .public_points(&[statement.v])
            .expect("cannot add statment");
        verifier_state.ratchet().expect("failed to wratchet");
        verify(verifier_state, &crs, &statement).expect("proof should verify")
    }
}
