mod common;

use ark_secp256k1::{Fr, Projective};
use bulletproofs::{
    circuit::{
        prove as circuit_prove,
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

struct ProofData {
    proof: Vec<u8>,
}

const BATCH_SIZE: usize = 50;

fn bench_circuit_prove_verify_cycle<Rng: rand::Rng>(
    c: &mut Criterion,
    crs: &CircuitCRS<Projective>,
    n: usize, // circuit dimension (number of multiplication gates)
    q: usize, // number of linear constraints
    m: usize, // number of public inpus
    rng: &mut Rng,
) {
    let mut group = c.benchmark_group(format!("circuit_{n}_{q}"));
    group.sample_size(10);
    group.measurement_time(std::time::Duration::from_secs(30));

    let mut proofs: BoundedProofQueue<(Circuit<Fr>, CircuitStatement<Projective>, ProofData)> =
        BoundedProofQueue::new(500);

    // Benchmark prove
    group.bench_with_input(
        BenchmarkId::new("prove", format!("{n}_{q}_{m}")),
        &(n, q, m),
        |b, _| {
            b.iter(|| {
                let (circuit, witness) = Circuit::<Fr>::generate_from_witness(q, n, m, rng);
                let statement: CircuitStatement<Projective> = CircuitStatement::new(crs, &witness);

                let domain_separator =
                    spongefish::domain_separator!("circuit-benchmark").instance(&statement);
                let mut prover_state = domain_separator.std_prover();

                let proof = circuit_prove(&mut prover_state, crs, &circuit, &witness, rng);
                let proof_data = ProofData { proof };
                proofs.push((circuit, statement, proof_data));
            })
        },
    );

    // Benchmark verify
    group.bench_with_input(
        BenchmarkId::new("verify", format!("{n}_{q}_{m}")),
        &(n, q),
        |b, _| {
            b.iter(|| {
                let (circuit, statement, proof_data) = proofs.choose(rng).unwrap();
                let domain_separator =
                    spongefish::domain_separator!("circuit-benchmark").instance(statement);
                let mut verifier_state = domain_separator.std_verifier(&proof_data.proof);

                circuit_verify(&mut verifier_state, crs, circuit, statement).unwrap();
            })
        },
    );

    // Benchmark batch verify
    group.bench_with_input(
        BenchmarkId::new("verify_batch", format!("{n}_{q}_{m}_{BATCH_SIZE}")),
        &(n, q),
        |b, _| {
            b.iter(|| {
                let selected_proofs = proofs.choose_multiple(rng, BATCH_SIZE);

                let verifications = selected_proofs
                    .into_par_iter()
                    .map(|(circuit, statement, proof_data)| {
                        let domain_separator =
                            spongefish::domain_separator!("circuit-benchmark").instance(statement);
                        let mut verifier_state = domain_separator.std_verifier(&proof_data.proof);
                        verify_aux(&mut verifier_state, crs, circuit, statement)
                    })
                    .collect::<Result<Vec<_>, _>>()
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
    let circuit_sizes: Vec<(u32, u32, usize)> = [2u32.pow(4), 2u32.pow(8), 2u32.pow(12)]
        .into_iter()
        .map(|n| (n, 3 * n, 10))
        .collect();
    for (n, q, m) in circuit_sizes {
        bench_circuit_prove_verify_cycle(c, &crs, n as usize, q as usize, m, &mut rng);
    }
}

criterion_group!(circuit_benches, bench_circuit_proofs);
criterion_main!(circuit_benches);
