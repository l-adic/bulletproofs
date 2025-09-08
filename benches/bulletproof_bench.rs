use std::collections::HashMap;

use ark_secp256k1::{Fr, Projective};
use bulletproofs::{
    circuit::{
        CircuitProofDomainSeparator, prove as circuit_prove,
        types::{CRS as CircuitCRS, Circuit, Statement as CircuitStatement},
        verify as circuit_verify,
    },
    ipa::{
        BulletproofDomainSeparator, prove as ipa_prove,
        types::{CRS as IpaCRS, CrsSize, Witness as IpaWitness},
        verify as ipa_verify,
    },
    range::{
        RangeProofDomainSeparator,
        aggregate::{
            AggregatedRangeProofDomainSeparator, prove as aggregate_prove,
            verify as aggregate_verify,
        },
        prove as range_prove,
        types::{
            self as range_types, CRS as RangeCRS, Statement as RangeStatement,
            Witness as RangeWitness,
        },
        verify as range_verify,
    },
};
use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use rand::{RngCore, rngs::OsRng};
use spongefish::DomainSeparator;
use spongefish::codecs::arkworks_algebra::CommonGroupToUnit;

fn bench_ipa_prove_verify_cycle(c: &mut Criterion) {
    let mut rng = OsRng;
    let mut group = c.benchmark_group("ipa");
    group.sample_size(10);
    group.measurement_time(std::time::Duration::from_secs(80));

    // Test different CRS sizes (log values)
    let sizes = [2_u64, 4, 8, 16];

    let mut proofs: HashMap<u64, Vec<u8>> = HashMap::new();

    for size in sizes {
        let crs_size = CrsSize { log2_size: size };
        let crs: IpaCRS<Projective> = IpaCRS::rand(crs_size, &mut rng);

        // Create shared domain separator
        let domain_separator = DomainSeparator::new("ipa-benchmark");
        let domain_separator =
            BulletproofDomainSeparator::<Projective>::bulletproof_statement(domain_separator)
                .ratchet();
        let domain_separator =
            BulletproofDomainSeparator::<Projective>::add_bulletproof(domain_separator, crs.size());

        let witness = IpaWitness::rand(crs.size() as u64, &mut rng);
        let stmt = witness.statement(&crs);

        // Benchmark prove
        group.bench_with_input(BenchmarkId::new("prove", size), &size, |b, _| {
            b.iter(|| {
                let mut prover_state = domain_separator.to_prover_state();
                prover_state.public_points(&[stmt.p]).unwrap();
                prover_state.ratchet().unwrap();

                let proof = ipa_prove(&mut prover_state, &crs, stmt, &witness).unwrap();
                proofs.insert(size, proof.clone());
                black_box(proof)
            })
        });

        // Benchmark verify using the same domain separator and pre-generated proof
        group.bench_with_input(BenchmarkId::new("verify", size), &size, |b, _| {
            b.iter(|| {
                let proof = proofs.get(&size).unwrap();
                let mut verifier_state = domain_separator.to_verifier_state(proof);
                verifier_state.public_points(&[stmt.p]).unwrap();
                verifier_state.ratchet().unwrap();

                ipa_verify(&mut verifier_state, &crs, &stmt).unwrap();
                black_box(())
            })
        });
    }

    group.finish();
}

fn bench_range_prove_verify_cycle(c: &mut Criterion, crs: &RangeCRS<Projective>, n_bits: usize) {
    let mut group = c.benchmark_group(format!("range_{}", n_bits));
    group.sample_size(10);
    group.measurement_time(std::time::Duration::from_secs(30));

    let mut rng = OsRng;

    let domain_separator = {
        let domain_separator = DomainSeparator::new("range-benchmark");
        let domain_separator =
            RangeProofDomainSeparator::<Projective>::range_proof_statement(domain_separator)
                .ratchet();
        RangeProofDomainSeparator::<Projective>::add_range_proof(domain_separator, n_bits)
    };

    let mut proofs: HashMap<RangeStatement<Projective>, Vec<u8>> = HashMap::new();

    let max_val = (1u64 << n_bits) - 1;
    let v = Fr::from(rng.next_u64() % max_val.max(1));
    let witness = RangeWitness::<Fr>::new(v, n_bits, &mut rng);
    let statement = RangeStatement::<Projective>::new(crs, &witness);

    // Benchmark prove
    group.bench_with_input(BenchmarkId::new("prove", n_bits), &n_bits, |b, _| {
        b.iter(|| {
            let mut prover_state = domain_separator.to_prover_state();
            prover_state.public_points(&[statement.v]).unwrap();
            prover_state.ratchet().unwrap();
            let proof =
                range_prove::<Projective, _>(prover_state, crs, &witness, &mut rng).unwrap();
            proofs.insert(statement.clone(), proof.clone());
            black_box(proof)
        })
    });

    // Benchmark verify using proof from HashMap
    group.bench_with_input(BenchmarkId::new("verify", n_bits), &n_bits, |b, _| {
        b.iter(|| {
            let proof = proofs.get(&statement).unwrap();
            let mut verifier_state = domain_separator.to_verifier_state(proof);
            verifier_state.public_points(&[statement.v]).unwrap();
            verifier_state.ratchet().unwrap();
            range_verify::<Projective>(&mut verifier_state, crs, &statement).unwrap();
            black_box(())
        })
    });

    group.finish();
}

fn bench_aggregate_range_prove_verify_cycle(
    c: &mut Criterion,
    crs: &RangeCRS<Projective>,
    n_bits: usize,
    m: usize,
) {
    let mut group = c.benchmark_group(format!("aggregate_range_{}_{}", n_bits, m));
    group.sample_size(10);
    group.measurement_time(std::time::Duration::from_secs(60));

    let mut rng = OsRng;

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

    let mut proofs: HashMap<range_types::aggregate::Statement<Projective>, Vec<u8>> =
        HashMap::new();

    // Generate m random values in range [0, 2^n_bits)
    let max_val = (1u128 << n_bits.min(127)) - 1;
    let v: Vec<Fr> = (0..m)
        .map(|_| Fr::from(rng.next_u64() as u128 % (max_val + 1)))
        .collect();

    let witness = range_types::aggregate::Witness::<Fr>::new(v, n_bits, &mut rng);
    let statement = range_types::aggregate::Statement::<Projective>::new(crs, &witness);

    // Benchmark prove
    group.bench_with_input(BenchmarkId::new("prove", m), &m, |b, _| {
        b.iter(|| {
            let mut prover_state = domain_separator.to_prover_state();
            prover_state.public_points(&statement.v).unwrap();
            prover_state.ratchet().unwrap();
            let proof =
                aggregate_prove::<Projective, _>(prover_state, crs, &witness, &mut rng).unwrap();
            proofs.insert(statement.clone(), proof.clone());
            black_box(proof)
        })
    });

    // Benchmark verify using proof from HashMap
    group.bench_with_input(BenchmarkId::new("verify", m), &m, |b, _| {
        b.iter(|| {
            let proof = proofs.get(&statement).unwrap();
            let mut verifier_state = domain_separator.to_verifier_state(proof);
            verifier_state.public_points(&statement.v).unwrap();
            verifier_state.ratchet().unwrap();
            aggregate_verify::<Projective>(&mut verifier_state, crs, &statement).unwrap();
            black_box(())
        })
    });

    group.finish();
}

fn bench_range_proofs(c: &mut Criterion) {
    let mut rng = OsRng;
    // Create shared CRS that's large enough for all range proof sizes we want to test
    let shared_crs = RangeCRS::rand(64, &mut rng);

    bench_range_prove_verify_cycle(c, &shared_crs, 8);
    bench_range_prove_verify_cycle(c, &shared_crs, 16);
    bench_range_prove_verify_cycle(c, &shared_crs, 32);
    bench_range_prove_verify_cycle(c, &shared_crs, 64);
}

fn bench_circuit_prove_verify_cycle(
    c: &mut Criterion,
    crs: &CircuitCRS<Projective>,
    n: usize, // circuit dimension (number of variables)
    q: usize, // number of constraints
) {
    let mut group = c.benchmark_group(format!("circuit_{}_{}", n, q));
    group.sample_size(10);
    group.measurement_time(std::time::Duration::from_secs(30));

    let mut rng = OsRng;

    // Generate circuit and witness
    let (circuit, witness) = Circuit::<Fr>::generate_from_witness(q, n, &mut rng);
    assert!(
        circuit.is_satisfied_by(&witness),
        "Circuit not satisfied by witness"
    );

    let domain_separator = {
        let domain_separator = DomainSeparator::new("circuit-benchmark");
        let domain_separator = CircuitProofDomainSeparator::<Projective>::circuit_proof_statement(
            domain_separator,
            witness.v.len(),
        )
        .ratchet();
        CircuitProofDomainSeparator::<Projective>::add_circuit_proof(domain_separator, n)
    };

    let statement: CircuitStatement<Projective> = CircuitStatement::new(crs, &witness);
    let mut proofs: HashMap<String, Vec<u8>> = HashMap::new();
    let key = format!("{}_{}", n, q);

    // Benchmark prove
    group.bench_with_input(
        BenchmarkId::new("prove", format!("{}_{}", n, q)),
        &(n, q),
        |b, _| {
            b.iter(|| {
                let mut prover_state = domain_separator.to_prover_state();
                prover_state.public_points(&statement.v).unwrap();
                prover_state.ratchet().unwrap();

                let proof =
                    circuit_prove(&mut prover_state, crs, &circuit, &witness, &mut rng).unwrap();
                proofs.insert(key.clone(), proof.clone());
                black_box(proof)
            })
        },
    );

    // Benchmark verify using the same domain separator and pre-generated proof
    group.bench_with_input(
        BenchmarkId::new("verify", format!("{}_{}", n, q)),
        &(n, q),
        |b, _| {
            b.iter(|| {
                let proof = proofs.get(&key).unwrap();
                let mut verifier_state = domain_separator.to_verifier_state(proof);
                let statement = CircuitStatement::new(crs, &witness);
                verifier_state.public_points(&statement.v).unwrap();
                verifier_state.ratchet().unwrap();

                circuit_verify(&mut verifier_state, crs, &circuit, statement).unwrap();
                black_box(())
            })
        },
    );

    group.finish();
}

fn bench_circuit_proofs(c: &mut Criterion) {
    let circuit_sizes = [(4, 8), (8, 16), (16, 32)];

    // Create CRS
    let crs: CircuitCRS<Projective> = CircuitCRS::rand(16, &mut OsRng);

    for (n, q) in circuit_sizes {
        bench_circuit_prove_verify_cycle(c, &crs, n, q);
    }
}

fn bench_aggregate_range_proofs(c: &mut Criterion) {
    // Create shared CRS large enough for n_bits=64 and m=512 (64 * 512 = 32768)
    let shared_crs = RangeCRS::rand(64 * 512, &mut OsRng);
    let n_bits = 64;

    // Test powers of 2 from 2^1 to 2^9 (2 to 512)
    for i in 1..=9 {
        let m = 1 << i; // 2^i
        bench_aggregate_range_prove_verify_cycle(c, &shared_crs, n_bits, m);
    }
}

criterion_group!(
    benches,
    bench_ipa_prove_verify_cycle,
    bench_range_proofs,
    bench_aggregate_range_proofs,
    bench_circuit_proofs,
);
criterion_main!(benches);
