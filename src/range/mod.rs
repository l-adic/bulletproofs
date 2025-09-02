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
use spongefish::codecs::arkworks_algebra::FieldToUnitSerialize;
use spongefish::codecs::arkworks_algebra::UnitToField;
use spongefish::{
    DomainSeparator, ProofResult, ProverState,
    codecs::arkworks_algebra::{FieldDomainSeparator, GroupDomainSeparator, GroupToUnitSerialize},
};
use std::array::from_fn;
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
        self.add_points(2, "Range proof statement")
    }

    /// The IO of the range proof protocol
    fn add_range_proof(mut self, n: usize) -> Self {
        for _ in 0..(n as f64).log2().ceil() as usize {
            self = self
                .add_points(2, "round-message")
                .challenge_scalars(1, "challenge");
        }
        self.add_scalars(2, "final-message")
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
        std::array::from_fn(|i| G::ScalarField::from(2u64).pow([i as u64]));

    let al: [G::ScalarField; N] = {
        let mut bits = bit_decomposition(witness.v);
        bits.resize(N, G::ScalarField::zero());
        bits.try_into().unwrap()
    };

    let ar: [G::ScalarField; N] = al.map(|x| x - G::ScalarField::one());

    let alpha: G::ScalarField = UniformRand::rand(rng);
    let a = crs.ipa_crs.u.mul(alpha)
        + G::msm_unchecked(&crs.ipa_crs.gs, &al)
        + G::msm_unchecked(&crs.ipa_crs.hs, &ar);
    let sl: [G::ScalarField; N] = from_fn(|_| UniformRand::rand(rng));
    let sr: [G::ScalarField; N] = from_fn(|_| UniformRand::rand(rng));

    let rho: G::ScalarField = UniformRand::rand(rng);
    let s = crs.ipa_crs.u.mul(rho)
        + G::msm_unchecked(&crs.ipa_crs.gs[0..N], &sl)
        + G::msm_unchecked(&crs.ipa_crs.hs[0..N], &sr);
    prover_state.add_points(&[a, s])?;
    let [y, z]: [G::ScalarField; 2] = prover_state.challenge_scalars()?;
    let y_n: [G::ScalarField; N] = from_fn(|i| y.pow([i as u64]));

    let l_vecpoly = {
        let coeffs = vec![std::array::from_fn(|i| al[i] - one_vec[i]), sl];
        VectorPolynomial { coeffs }
    };

    let r_vecpoly = {
        let coeffs = vec![
            from_fn(|i| y_n[i] * (ar[i] + one_vec[i] * z) + two_vec[i] * z.square()),
            sr,
        ];
        VectorPolynomial { coeffs }
    };

    let t_poly = l_vecpoly.inner_product(&r_vecpoly);

    let tao1: G::ScalarField = UniformRand::rand(rng);
    let tao2: G::ScalarField = UniformRand::rand(rng);

    let tt1 = crs.g.mul(tao1) + crs.h.mul(t_poly[1]);
    let tt2 = crs.g.mul(tao2) + crs.h.mul(t_poly[2]);

    prover_state.add_points(&[tt1, tt2])?;

    let [x]: [G::ScalarField; 1] = prover_state.challenge_scalars()?;

    let l: [G::ScalarField; N] = l_vecpoly.evaluate(x);
    let r: [G::ScalarField; N] = r_vecpoly.evaluate(x);
    let t_hat = dot(&l, &r);
    let tao_x = tao2 * x.square() + tao1 * x + witness.gamma * z.square();
    let mu = alpha + rho * x;

    prover_state.add_scalars(&[tao_x, mu, t_hat])?;
    prover_state.add_scalars(&l)?;
    prover_state.add_scalars(&r)?;

    Ok(Vec::new())
}
