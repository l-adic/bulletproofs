pub mod common;

use ark_ec::PrimeGroup;
use ark_ff::UniformRand;
use ark_poly::univariate::DensePolynomial;
use ark_secp256k1::Projective;
use bulletproofs::{
    ipa::types::CrsSize,
    poly_commit::{
        prove as poly_prove,
        types::{CRS, Statement, Witness},
        verify as poly_verify,
    },
};
use common::BoundedProofQueue;
use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use rand::rngs::OsRng;

type Fr = <ark_ec::short_weierstrass::Projective<ark_secp256k1::Config> as PrimeGroup>::ScalarField;

struct ProofData {
    proof: Vec<u8>,
    statement: Statement<Projective>,
    todo: bulletproofs::poly_commit::Todo<Projective>,
}

const BATCH_SIZES: &[usize] = &[10, 100];

fn bench_single_poly_commit<Rng: rand::Rng>(
    c: &mut Criterion,
    crs_log2_size: usize,
    crs: &CRS<Projective>,
    rng: &mut Rng,
) -> BoundedProofQueue<ProofData> {
    let mut group = c.benchmark_group("poly_commit_single");
    group.sample_size(10);

    let poly_degree = crs.size() - 1;

    let mut proofs: BoundedProofQueue<ProofData> = BoundedProofQueue::new(500);

    group.bench_with_input(
        BenchmarkId::new("prove", crs_log2_size),
        &crs_log2_size,
        |b, _| {
            b.iter(|| {
                let witness: Witness<Projective, DensePolynomial<Fr>> =
                    Witness::rand(poly_degree, rng);
                let x = Fr::rand(rng);
                let statement = witness.statement(crs, x);

                let domain_separator =
                    spongefish::domain_separator!("poly-commit-benchmark").instance(&statement);
                let mut prover_state = domain_separator.std_prover();

                let todo = poly_prove(&mut prover_state, crs, &statement, &witness, rng);
                let proof_data = ProofData {
                    proof: prover_state.narg_string().to_vec(),
                    statement,
                    todo,
                };
                proofs.push(proof_data);
            })
        },
    );

    group.bench_with_input(
        BenchmarkId::new("verify", crs_log2_size),
        &crs_log2_size,
        |b, _| {
            b.iter(|| {
                let proof_data = proofs.choose(rng).unwrap();
                let domain_separator = spongefish::domain_separator!("poly-commit-benchmark")
                    .instance(&proof_data.statement);
                let mut verifier_state = domain_separator.std_verifier(&proof_data.proof);
                poly_verify(&mut verifier_state, crs, &proof_data.statement).unwrap();
            })
        },
    );

    group.finish();
    proofs
}

fn bench_aggregated_poly_commit<Rng: rand::Rng>(
    c: &mut Criterion,
    crs_log2_size: usize,
    crs: &CRS<Projective>,
    proofs_queue: &BoundedProofQueue<ProofData>,
    rng: &mut Rng,
) {
    let mut group = c.benchmark_group("poly_commit_aggregated");
    group.sample_size(10);

    for &batch_size in BATCH_SIZES {
        group.bench_with_input(
            BenchmarkId::new(
                "lazy_verify_and_aggregate",
                format!("{crs_log2_size}_batch_{batch_size}"),
            ),
            &batch_size,
            |b, _| {
                b.iter(|| {
                    // Select random batch of proofs from the queue
                    let selected_proofs = proofs_queue.choose_multiple(rng, batch_size);

                    // Accumulate todos using lazy_verify for actual batch verification
                    let verifier_todos = selected_proofs
                        .iter()
                        .try_fold(Vec::new(), |todos, proof_data| {
                            let domain_separator =
                                spongefish::domain_separator!("poly-commit-benchmark")
                                    .instance(&proof_data.statement);
                            let mut verifier_state =
                                domain_separator.std_verifier(&proof_data.proof);
                            bulletproofs::poly_commit::lazy_verify(
                                &mut verifier_state,
                                crs,
                                &proof_data.statement,
                                proof_data.todo.g,
                                todos,
                            )
                        })
                        .unwrap();

                    // Extract prover todos for comparison and folding
                    let prover_todos: Vec<bulletproofs::poly_commit::Todo<Projective>> =
                        selected_proofs
                            .iter()
                            .map(|proof_data| proof_data.todo.clone())
                            .collect();

                    // Verify todos match (this would be an assertion in tests)
                    assert_eq!(prover_todos, verifier_todos);

                    // Perform actual batch verification using the accumulated todos
                    let alpha = ark_ff::UniformRand::rand(&mut *rng);
                    let x = ark_ff::UniformRand::rand(&mut *rng);
                    let witness =
                        bulletproofs::poly_commit::fold_todos_witness(&prover_todos, alpha);
                    let statement =
                        bulletproofs::poly_commit::fold_todos_statement(&verifier_todos, alpha, x);

                    // Final batched proof verification
                    let domain_separator =
                        spongefish::domain_separator!("poly-commit-benchmark").instance(&statement);
                    let mut prover_state = domain_separator.std_prover();
                    let _final_todo = bulletproofs::poly_commit::prove(
                        &mut prover_state,
                        crs,
                        &statement,
                        &witness,
                        &mut *rng,
                    );
                    let proof = prover_state.narg_string().to_vec();
                    let mut verifier_state = domain_separator.std_verifier(&proof);
                    bulletproofs::poly_commit::verify(&mut verifier_state, crs, &statement)
                        .unwrap();

                    black_box(())
                })
            },
        );
    }

    group.finish();
}

fn bench_poly_commit_proofs(c: &mut Criterion) {
    let mut rng = OsRng;

    // Test various CRS sizes: 2^4, 2^8, 2^12, 2^16
    for crs_log2_size in [4, 8, 12, 16] {
        println!(
            "Generating CRS of size 2^{} = {}",
            crs_log2_size,
            1 << crs_log2_size
        );
        let crs_size = CrsSize {
            log2_size: crs_log2_size as u64,
        };
        let crs: CRS<Projective> = CRS::rand(crs_size, &mut rng);

        let proofs = bench_single_poly_commit(c, crs_log2_size, &crs, &mut rng);
        bench_aggregated_poly_commit(c, crs_log2_size, &crs, &proofs, &mut rng);
    }
}

criterion_group!(poly_commit_benches, bench_poly_commit_proofs);
criterion_main!(poly_commit_benches);
