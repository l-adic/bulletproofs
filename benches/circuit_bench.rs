mod common;

use ark_secp256k1::{Fr, Projective};
use bulletproofs::{
    circuit::{
        CircuitProofDomainSeparator, prove as circuit_prove,
        types::{CRS as CircuitCRS, Circuit, Statement as CircuitStatement},
        verify as circuit_verify, verify_aux,
    },
    msm::verify_batch_aux,
};
use common::BoundedProofQueue;
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use nonempty::NonEmpty;
use rand::rngs::OsRng;
use rayon::prelude::*;
use spongefish::{DomainSeparator, ProofError, codecs::arkworks_algebra::CommonGroupToUnit};

struct ProofData {
    proof: Vec<u8>,
    domain_separator: DomainSeparator,
}

const BATCH_SIZE: usize = 50;

fn bench_circuit_prove_verify_cycle<Rng: rand::Rng>(
    c: &mut Criterion,
    crs: &CircuitCRS<Projective>,
    n: usize, // circuit dimension (number of variables)
    q: usize, // number of constraints
    rng: &mut Rng,
) {
    let mut group = c.benchmark_group(format!("circuit_{}_{}", n, q));
    group.sample_size(10);
    group.measurement_time(std::time::Duration::from_secs(30));

    let domain_separator = {
        let domain_separator = DomainSeparator::new("circuit-benchmark");
        let domain_separator =
            CircuitProofDomainSeparator::<Projective>::circuit_proof_statement(domain_separator, n)
                .ratchet();
        CircuitProofDomainSeparator::<Projective>::add_circuit_proof(domain_separator, n)
    };

    let mut proofs: BoundedProofQueue<(Circuit<Fr>, CircuitStatement<Projective>, ProofData)> =
        BoundedProofQueue::new(500);

    // Benchmark prove
    group.bench_with_input(
        BenchmarkId::new("prove", format!("{}_{}", n, q)),
        &(n, q),
        |b, _| {
            b.iter(|| {
                let (circuit, witness) = Circuit::<Fr>::generate_from_witness(q, n, rng);
                let statement: CircuitStatement<Projective> = CircuitStatement::new(crs, &witness);
                let mut prover_state = domain_separator.to_prover_state();
                prover_state.public_points(&statement.v).unwrap();
                prover_state.ratchet().unwrap();

                let proof = circuit_prove(&mut prover_state, crs, &circuit, &witness, rng).unwrap();
                let proof_data = ProofData {
                    proof: proof.clone(),
                    domain_separator: domain_separator.clone(),
                };
                proofs.push((circuit, statement, proof_data));
            })
        },
    );

    // Benchmark verify using the same domain separator and pre-generated proof
    group.bench_with_input(
        BenchmarkId::new("verify", format!("{}_{}", n, q)),
        &(n, q),
        |b, _| {
            b.iter(|| {
                let (circuit, statement, proof_data) = proofs.choose(rng).unwrap();
                let mut verifier_state = proof_data
                    .domain_separator
                    .to_verifier_state(&proof_data.proof);
                verifier_state.public_points(&statement.v).unwrap();
                verifier_state.ratchet().unwrap();

                circuit_verify(&mut verifier_state, crs, circuit, statement, rng).unwrap();
            })
        },
    );

    // Benchmark batch verify
    group.bench_with_input(
        BenchmarkId::new("verify_batch", format!("{}_{}", n, q)),
        &(n, q),
        |b, _| {
            b.iter(|| {
                let selected_proofs = proofs.choose_multiple(rng, BATCH_SIZE);

                let verifications = selected_proofs
                    .into_par_iter()
                    .map(|(circuit, statement, proof_data)| {
                        let mut verifier_state = proof_data
                            .domain_separator
                            .to_verifier_state(&proof_data.proof);
                        verifier_state.public_points(&statement.v)?;
                        verifier_state.ratchet().unwrap();
                        verify_aux(&mut verifier_state, crs, circuit, statement, &mut OsRng)
                    })
                    .collect::<Result<Vec<_>, ProofError>>()
                    .unwrap();

                let verifications = NonEmpty::from_vec(verifications).expect("non-empty vec");
                verify_batch_aux(verifications, &mut OsRng).expect("should verify batch");
            })
        },
    );

    group.finish();
}

fn bench_circuit_proofs(c: &mut Criterion) {
    let mut rng = OsRng;
    let crs: CircuitCRS<Projective> = CircuitCRS::rand(2u32.pow(20) as usize, &mut rng);
    let circuit_sizes = [
        (2u32.pow(4), 2u32.pow(8)),
        (2u32.pow(8), 2u32.pow(12)),
        (2u32.pow(12), 2u32.pow(16)),
    ];
    for (n, q) in circuit_sizes {
        bench_circuit_prove_verify_cycle(c, &crs, n as usize, q as usize, &mut rng);
    }
}

criterion_group!(circuit_benches, bench_circuit_proofs);
criterion_main!(circuit_benches);
