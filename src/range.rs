use ark_ff::{BigInteger, PrimeField};

pub struct Witness<Fr> {
    pub v: Fr,
    pub gamma: Fr,
}

// Will always return a vector of length equal to the field's modulus bit size,
// e.g. for a 256-bit prime field, it will return a vector of 256 bits.
pub fn bit_decomposition<Fr: PrimeField>(x: Fr) -> Vec<Fr> {
    let mut bits = Vec::new();
    let mut x = x.into_bigint();
    let num_bits = Fr::MODULUS_BIT_SIZE;
    for _ in 0..num_bits {
        bits.push(x.is_odd().into());
        x.div2();
    }
    bits
}
