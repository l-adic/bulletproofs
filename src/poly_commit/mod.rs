use crate::{
    ipa::{
        extended::{self, ExtendedBulletproofDomainSeparator},
        types::{CRS, Witness as IpaWitness, extended::Statement as ExtendedIpaStatement},
    },
    msm::Msm,
};
use ark_ec::CurveGroup;
use ark_ff::{Field, Zero};
use ark_poly::{
    Polynomial,
    polynomial::{self, DenseUVPolynomial},
};
use spongefish::{
    DomainSeparator, ProofResult, ProverState, VerifierState,
    codecs::arkworks_algebra::{FieldDomainSeparator, GroupDomainSeparator},
};
use std::marker::PhantomData;

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

    fn add_opening_proof(self, len: usize) -> Self {
        self.add_extended_bulletproof(len)
    }
}

pub struct PolyCommit<G: CurveGroup> {
    pub g: G,
}

impl<G: CurveGroup> CRS<G> {
    fn commit<P: DenseUVPolynomial<G::ScalarField>>(&self, f: &P) -> PolyCommit<G> {
        assert!(
            f.degree() <= self.size(),
            "Cannot commit to polynomial of degree higher than the crs size"
        );
        let mut coeffs = f.coeffs().to_vec();
        coeffs.resize(self.size(), G::ScalarField::zero());
        let g = G::msm_unchecked(&self.gs, f.coeffs());
        PolyCommit { g }
    }
}

#[derive(Debug)]
pub struct Witness<G: CurveGroup, P: DenseUVPolynomial<G::ScalarField>> {
    pub p: P,
    _group: PhantomData<G>,
}

impl<G: CurveGroup, P: DenseUVPolynomial<G::ScalarField>> Witness<G, P> {
    pub fn statement(&self, crs: &CRS<G>, x: G::ScalarField) -> Statement<G> {
        let commitment = crs.commit(&self.p);
        let evaluation = self.p.evaluate(&x);
        Statement {
            commitment,
            evaluation,
            x,
        }
    }
}

impl<G: CurveGroup> Witness<G, polynomial::univariate::DensePolynomial<G::ScalarField>> {
    pub fn rand<Rng: rand::Rng>(degree: usize, rng: &mut Rng) -> Self {
        let p = polynomial::univariate::DensePolynomial::rand(degree, rng);
        Witness {
            p,
            _group: PhantomData,
        }
    }

    pub fn size(&self) -> usize {
        self.p.degree() + 1
    }
}

fn powers_of_x<F: Field>(x: F) -> impl Iterator<Item = F> {
    (0..).scan(F::one(), move |state, _| {
        let current = *state;
        *state = state.mul(x);
        Some(current)
    })
}

impl<G: CurveGroup, P: DenseUVPolynomial<G::ScalarField>> Witness<G, P> {
    pub fn into_ipa_witness(&self, x: G::ScalarField) -> IpaWitness<G> {
        IpaWitness {
            a: self.p.coeffs().to_vec(),
            b: powers_of_x(x).take(self.p.coeffs().len()).collect(),
            c: self.p.evaluate(&x),
        }
    }
}

pub struct Statement<G: CurveGroup> {
    pub commitment: PolyCommit<G>,
    pub x: G::ScalarField,
    pub evaluation: G::ScalarField,
}

impl<G: CurveGroup> Statement<G> {
    pub fn extended_statement(&self, crs: &CRS<G>) -> ExtendedIpaStatement<G> {
        let xs: Vec<G::ScalarField> = powers_of_x(self.x).take(crs.hs.len()).collect();
        let h = G::msm_unchecked(&crs.hs, &xs);
        ExtendedIpaStatement {
            p: self.commitment.g.add(h),
            c: self.evaluation,
            witness_size: crs.size(),
        }
    }
}

pub fn prove<G: CurveGroup, P: DenseUVPolynomial<G::ScalarField>>(
    prover_state: &mut ProverState,
    crs: &CRS<G>,
    statement: &Statement<G>,
    witness: &Witness<G, P>,
) -> ProofResult<Vec<u8>> {
    let ipa_witness = witness.into_ipa_witness(statement.x);
    let ext_statement = statement.extended_statement(crs);
    extended::prove(prover_state, crs, &ext_statement, &ipa_witness)
}

pub fn verify_aux<G: CurveGroup>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
) -> ProofResult<Msm<G>> {
    let ext_statement = statement.extended_statement(crs);
    extended::verify_aux(verifier_state, crs, &ext_statement)
}

pub fn verify<G: CurveGroup>(
    verifier_state: &mut VerifierState,
    crs: &CRS<G>,
    statement: &Statement<G>,
) -> ProofResult<()> {
    let ext_statement = statement.extended_statement(crs);
    extended::verify(verifier_state, crs, &ext_statement)
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

    proptest! {
      #![proptest_config(Config::with_cases(2))]
      #[test]
      fn test_poly_comm_prove_verify_works((crs, witness, x) in any::<CrsSize>().prop_map(|crs_size| {
          let mut rng = OsRng;
          type Fr = <ark_ec::short_weierstrass::Projective<ark_secp256k1::Config> as PrimeGroup>::ScalarField;
          let crs: CRS<Projective> = CRS::rand(crs_size, &mut rng);
          let n = crs.size() as u64;
          let witness: Witness<Projective, DensePolynomial<Fr>> = Witness::rand((n - 1) as usize, &mut rng);
          let x = Fr::rand(&mut rng);
          (crs, witness, x)
      })) {

            {

              let domain_separator = {
                let domain_separator = DomainSeparator::new("test-poly-comm");
                // add the IO of the bulletproof statement
                let domain_separator =
                    OpeningProofDomainSeparator::<Projective>::opening_proof_statement(domain_separator).ratchet();
                // add the IO of the bulletproof protocol (the transcript)
                OpeningProofDomainSeparator::<Projective>::add_opening_proof(domain_separator, witness.size())
              };

              let (statement, proof) = {

                let statement: Statement<Projective> = witness.statement(&crs, x);
                let mut prover_state = domain_separator.to_prover_state();
                prover_state.public_points(&[statement.commitment.g]).unwrap();
                prover_state.public_scalars(&[statement.x]).unwrap();
                prover_state.public_scalars(&[statement.evaluation]).unwrap();
                prover_state.ratchet().unwrap();
                let proof = prove(&mut prover_state, &crs, &statement, &witness).expect("proof should be generated");
                (statement, proof)
              };


              let mut verifier_state = domain_separator.to_verifier_state(&proof);
              verifier_state.public_points(&[statement.commitment.g]).expect("cannot add statement");
              verifier_state.public_scalars(&[statement.x]).expect("cannot add statement");
              verifier_state.public_scalars(&[statement.evaluation]).expect("cannot add statement");
              verifier_state.ratchet().expect("failed to ratchet");
              verify(&mut verifier_state, &crs, &statement).expect("proof should verify");

            }

      }
    }
}
