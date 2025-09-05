use ark_ff::Field;

// Matrix multiplication of a row vector x (1 x m) with a matrix m (m x n)
pub fn mat_mul_l<Fr: Field>(x: &[Fr], m: &[Vec<Fr>]) -> Vec<Fr> {
    assert_eq!(x.len(), m.len(), "Matrix multiplication dimension mismatch");
    let n = m[0].len();
    let mut res = vec![Fr::zero(); n];
    for (j, res_j) in res.iter_mut().enumerate() {
        for (i, x_i) in x.iter().enumerate() {
            *res_j += *x_i * m[i][j];
        }
    }
    res
}

pub fn mat_mul_r<Fr: Field>(m: &[Vec<Fr>], x: &[Fr]) -> Vec<Fr> {
    assert_eq!(
        m[0].len(),
        x.len(),
        "Matrix multiplication dimension mismatch"
    );
    let n = m.len();
    let mut res = vec![Fr::zero(); n];
    for (i, res_i) in res.iter_mut().enumerate() {
        for (j, x_j) in x.iter().enumerate() {
            *res_i += m[i][j] * *x_j;
        }
    }
    res
}

pub fn hadarmard<Fr: Field>(a: &[Fr], b: &[Fr]) -> Vec<Fr> {
    assert_eq!(a.len(), b.len(), "Hadamard product dimension mismatch");
    a.iter().zip(b.iter()).map(|(x, y)| *x * *y).collect()
}
