mod common;

use ark_secp256k1::{Fr, Projective};
use bulletproofs::circuit::{
    CircuitProofDomainSeparator, prove as circuit_prove,
    types::{CRS as CircuitCRS, Circuit, Statement as CircuitStatement},
    verify as circuit_verify,
};
use common::BoundedProofQueue;
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use rand::rngs::OsRng;
use spongefish::{DomainSeparator, codecs::arkworks_algebra::CommonGroupToUnit};

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

    let mut proofs: BoundedProofQueue<(Circuit<Fr>, CircuitStatement<Projective>, Vec<u8>)> =
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
                proofs.push((circuit, statement, proof));
            })
        },
    );

    // Benchmark verify using the same domain separator and pre-generated proof
    group.bench_with_input(
        BenchmarkId::new("verify", format!("{}_{}", n, q)),
        &(n, q),
        |b, _| {
            b.iter(|| {
                let (circuit, statement, proof) = proofs.choose(rng).unwrap();
                let mut verifier_state = domain_separator.to_verifier_state(proof);
                verifier_state.public_points(&statement.v).unwrap();
                verifier_state.ratchet().unwrap();

                circuit_verify(&mut verifier_state, crs, circuit, statement).unwrap();
            })
        },
    );

    group.finish();
}

fn bench_circuit_proofs(c: &mut Criterion) {
    let mut rng = OsRng;
    let crs: CircuitCRS<Projective> = CircuitCRS::rand(16, &mut rng);
    let circuit_sizes = [(4, 8), (8, 16), (16, 32)];
    for (n, q) in circuit_sizes {
        bench_circuit_prove_verify_cycle(c, &crs, n, q, &mut rng);
    }
}

criterion_group!(circuit_benches, bench_circuit_proofs);
criterion_main!(circuit_benches);
