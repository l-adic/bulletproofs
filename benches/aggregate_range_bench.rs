mod common;

use crate::common::BoundedProofQueue;
use ark_secp256k1::{Fr, Projective};
use bulletproofs::{
    msm::verify_batch_aux,
    range::{
        aggregate::{
            AggregatedRangeProofDomainSeparator, prove as aggregate_prove,
            verify as aggregate_verify, verify_aux,
        },
        types::{self as range_types, CRS as RangeCRS, aggregate::Statement},
    },
};
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use nonempty::NonEmpty;
use rand::rngs::OsRng;
use rayon::prelude::*;
use spongefish::{DomainSeparator, ProofError, codecs::arkworks_algebra::CommonGroupToUnit};

struct ProofData {
    proof: Vec<u8>,
    domain_separator: DomainSeparator,
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

    let domain_separator = {
        let domain_separator = DomainSeparator::new("aggregate-range-benchmark");
        let domain_separator =
            AggregatedRangeProofDomainSeparator::<Projective>::aggregated_range_proof_statement(
                domain_separator,
                m,
            )
            .ratchet();
        AggregatedRangeProofDomainSeparator::<Projective>::add_aggregated_range_proof(
            domain_separator,
            n_bits,
            m,
        )
    };

    let mut proofs: BoundedProofQueue<(Statement<Projective>, ProofData)> =
        BoundedProofQueue::new(500);

    group.bench_with_input(BenchmarkId::new("prove", m), &m, |b, _| {
        b.iter(|| {
            // Generate m random values in range [0, 2^n_bits)
            let v: Vec<Fr> = (0..m).map(|_| Fr::from(rng.next_u64())).collect();

            let witness = range_types::aggregate::Witness::<Fr>::new(v, n_bits, rng);
            let statement = range_types::aggregate::Statement::<Projective>::new(crs, &witness);

            let mut prover_state = domain_separator.to_prover_state();
            prover_state.public_points(&statement.v).unwrap();
            prover_state.ratchet().unwrap();
            let proof = aggregate_prove::<Projective, _>(prover_state, crs, &witness, rng).unwrap();
            let proof_data = ProofData {
                proof: proof.clone(),
                domain_separator: domain_separator.clone(),
            };
            proofs.push((statement, proof_data));
        })
    });

    group.bench_with_input(BenchmarkId::new("verify", m), &m, |b, _| {
        b.iter(|| {
            let (statement, proof_data) = proofs.choose(rng).unwrap();
            let mut verifier_state = domain_separator.to_verifier_state(&proof_data.proof);
            verifier_state.public_points(&statement.v).unwrap();
            verifier_state.ratchet().unwrap();
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
                        ProofData {
                            proof,
                            domain_separator,
                        },
                    )| {
                        let mut verifier_state = domain_separator.to_verifier_state(proof);
                        verifier_state.public_points(&statement.v)?;
                        verifier_state.ratchet().unwrap();
                        verify_aux(&mut verifier_state, crs, statement, &mut OsRng)
                    },
                )
                .collect::<Result<Vec<_>, ProofError>>()
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
