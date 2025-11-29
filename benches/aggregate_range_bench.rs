mod common;

use crate::common::BoundedProofQueue;
use ark_secp256k1::{Fr, Projective};
use bulletproofs::{
    msm::verify_batch_aux,
    range::{
        aggregate::{
            prove as aggregate_prove,
            verify as aggregate_verify, verify_aux,
        },
        types::{self as range_types, CRS as RangeCRS, aggregate::Statement},
    },
};
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use nonempty::NonEmpty;
use rand::rngs::OsRng;
use rayon::prelude::*;

struct ProofData {
    proof: Vec<u8>,
}

const BATCH_SIZE: usize = 100;

fn bench_aggregate_range_prove_verify_cycle<Rng: rand::Rng>(
    c: &mut Criterion,
    crs: &RangeCRS<Projective>,
    n_bits: usize,
    m: usize,
    rng: &mut Rng,
) {
    let mut group = c.benchmark_group(format!("aggregate_range_{}_{}", n_bits, m));
    group.sample_size(10);
    group.measurement_time(std::time::Duration::from_secs(60));

    // Domain separator will be created per proof using the new API

    let mut proofs: BoundedProofQueue<(Statement<Projective>, ProofData)> =
        BoundedProofQueue::new(500);

    group.bench_with_input(BenchmarkId::new("prove", m), &m, |b, _| {
        b.iter(|| {
            // Generate m random values in range [0, 2^n_bits)
            let v: Vec<Fr> = (0..m).map(|_| Fr::from(rng.next_u64())).collect();

            let witness = range_types::aggregate::Witness::<Fr>::new(v, n_bits, rng);
            let statement = range_types::aggregate::Statement::<Projective>::new(crs, &witness);

            let domain_separator = spongefish::domain_separator!("aggregate-range-benchmark")
                .instance(&0u8);
            let prover_state = domain_separator.std_prover();
            
            let proof = aggregate_prove::<Projective, _>(prover_state, crs, &witness, rng);
            let proof_data = ProofData { proof };
            proofs.push((statement, proof_data));
        })
    });

    group.bench_with_input(BenchmarkId::new("verify", m), &m, |b, _| {
        b.iter(|| {
            let (statement, proof_data) = proofs.choose(rng).unwrap();
            let domain_separator = spongefish::domain_separator!("aggregate-range-benchmark")
                .instance(&0u8);
            let mut verifier_state = domain_separator.std_verifier(&proof_data.proof);
            aggregate_verify::<Projective, _>(&mut verifier_state, crs, statement, rng).unwrap();
        })
    });

    group.bench_with_input(BenchmarkId::new("verify_batch", m), &m, |b, _| {
        b.iter(|| {
            let selected_proofs = proofs.choose_multiple(rng, BATCH_SIZE);

            let verifications = selected_proofs
                .into_par_iter()
                .map(
                    |(
                        statement,
                        ProofData { proof },
                    )| {
                        let domain_separator = spongefish::domain_separator!("aggregate-range-benchmark")
                            .instance(&0u8);
                        let mut verifier_state = domain_separator.std_verifier(proof);
                        verify_aux(&mut verifier_state, crs, statement, &mut OsRng)
                    },
                )
                .collect::<Result<Vec<_>, _>>()
                .unwrap();

            let verifications = NonEmpty::from_vec(verifications).expect("non-empty vec");
            verify_batch_aux(verifications, &mut OsRng).expect("should verify batch");
        })
    });

    group.finish();
}

fn bench_aggregate_range_proofs(c: &mut Criterion) {
    let mut rng = OsRng;
    // Create shared CRS large enough for n_bits=64 and m=512 (64 * 512 = 32768)
    let shared_crs = RangeCRS::rand(64 * 512, &mut rng);
    let n_bits = 64;
    for i in 1..=9 {
        let m = 1 << i; // 2^i
        bench_aggregate_range_prove_verify_cycle(c, &shared_crs, n_bits, m, &mut rng);
    }
}

criterion_group!(aggregate_range_benches, bench_aggregate_range_proofs);
criterion_main!(aggregate_range_benches);
