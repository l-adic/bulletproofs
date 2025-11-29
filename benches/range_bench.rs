mod common;

use ark_secp256k1::{Fr, Projective};
use bulletproofs::{
    msm::verify_batch_aux,
    range::{
        prove as range_prove,
        types::{CRS as RangeCRS, Statement as RangeStatement, Witness as RangeWitness},
        verify as range_verify, verify_aux,
    },
};
use common::BoundedProofQueue;
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use nonempty::NonEmpty;
use rand::rngs::OsRng;
use rayon::prelude::*;

struct ProofData {
    proof: Vec<u8>,
}

const BATCH_SIZE: usize = 100;

fn bench_range_prove_verify_cycle<Rng: rand::Rng>(
    c: &mut Criterion,
    crs: &RangeCRS<Projective>,
    n_bits: usize,
    rng: &mut Rng,
) {
    let mut group = c.benchmark_group(format!("range_{}", n_bits));
    group.sample_size(10);
    group.measurement_time(std::time::Duration::from_secs(30));

    // Domain separator will be created per proof using the new API

    let mut proofs: BoundedProofQueue<(RangeStatement<Projective>, ProofData)> =
        BoundedProofQueue::new(500);

    group.bench_with_input(BenchmarkId::new("prove", n_bits), &n_bits, |b, _| {
        b.iter(|| {
            let max_value = (1u128 << n_bits) - 1;
            let v = Fr::from(rand::Rng::gen_range(rng, 0u128..=max_value));
            let witness = RangeWitness::<Fr>::new(v, n_bits, rng);
            let statement = RangeStatement::<Projective>::new(crs, &witness);
            
            let domain_separator = spongefish::domain_separator!("range-benchmark")
                .instance(&0u8);
            let prover_state = domain_separator.std_prover();
            
            let proof = range_prove::<Projective, _>(prover_state, crs, &witness, rng);
            let proof_data = ProofData { proof };
            proofs.push((statement, proof_data));
        })
    });

    group.bench_with_input(BenchmarkId::new("verify", n_bits), &n_bits, |b, _| {
        b.iter(|| {
            let (statement, proof_data) = proofs.choose(rng).unwrap();
            let domain_separator = spongefish::domain_separator!("range-benchmark")
                .instance(&0u8);
            let mut verifier_state = domain_separator.std_verifier(&proof_data.proof);
            range_verify::<Projective, _>(&mut verifier_state, crs, statement, rng).unwrap();
        })
    });

    group.bench_with_input(BenchmarkId::new("verify_batch", n_bits), &n_bits, |b, _| {
        b.iter(|| {
            let selected_proofs = proofs.choose_multiple(rng, BATCH_SIZE);

            let verifications = selected_proofs
                .into_par_iter()
                .map(
                    |(
                        statement,
                        ProofData { proof },
                    )| {
                        let domain_separator = spongefish::domain_separator!("range-benchmark")
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

fn bench_range_proofs(c: &mut Criterion) {
    let mut rng = OsRng;
    // Create shared CRS that's large enough for all range proof sizes we want to test
    let shared_crs = RangeCRS::rand(64, &mut rng);

    [8, 16, 32, 64].iter().for_each(|&n_bits| {
        bench_range_prove_verify_cycle(c, &shared_crs, n_bits, &mut rng);
    });
}

criterion_group!(range_benches, bench_range_proofs);
criterion_main!(range_benches);
