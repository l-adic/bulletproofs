use ark_ff::{Field, Zero};
use std::borrow::Borrow;
use std::ops::{Add, Mul, Sub};

pub struct VectorAdd<I1, I2> {
    iter1: I1,
    iter2: I2,
}

impl<I1, I2> Iterator for VectorAdd<I1, I2>
where
    I1: Iterator,
    I2: Iterator<Item = I1::Item>,
    I1::Item: Add<Output = I1::Item>,
{
    type Item = I1::Item;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.iter1.next(), self.iter2.next()) {
            (Some(a), Some(b)) => Some(a + b),
            _ => None,
        }
    }
}

pub struct VectorSub<I1, I2> {
    iter1: I1,
    iter2: I2,
}

impl<I1, I2> Iterator for VectorSub<I1, I2>
where
    I1: Iterator,
    I2: Iterator<Item = I1::Item>,
    I1::Item: Sub<Output = I1::Item>,
{
    type Item = I1::Item;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.iter1.next(), self.iter2.next()) {
            (Some(a), Some(b)) => Some(a - b),
            _ => None,
        }
    }
}

pub struct VectorHadamard<I1, I2> {
    iter1: I1,
    iter2: I2,
}

impl<I1, I2> Iterator for VectorHadamard<I1, I2>
where
    I1: Iterator,
    I2: Iterator<Item = I1::Item>,
    I1::Item: Mul<Output = I1::Item>,
{
    type Item = I1::Item;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.iter1.next(), self.iter2.next()) {
            (Some(a), Some(b)) => Some(a * b),
            _ => None,
        }
    }
}

pub struct VectorScale<I, T> {
    iter: I,
    scalar: T,
}

impl<I, T> Iterator for VectorScale<I, T>
where
    I: Iterator,
    T: Copy + Mul<I::Item, Output = I::Item>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|x| self.scalar * x)
    }
}

pub trait VectorOps: Iterator + Sized {
    fn vector_add<I>(self, other: I) -> VectorAdd<Self, I::IntoIter>
    where
        I: IntoIterator<Item = Self::Item>,
        Self::Item: Add<Output = Self::Item>,
    {
        VectorAdd {
            iter1: self,
            iter2: other.into_iter(),
        }
    }

    fn vector_sub<I>(self, other: I) -> VectorSub<Self, I::IntoIter>
    where
        I: IntoIterator<Item = Self::Item>,
        Self::Item: Sub<Output = Self::Item>,
    {
        VectorSub {
            iter1: self,
            iter2: other.into_iter(),
        }
    }

    fn hadamard<I>(self, other: I) -> VectorHadamard<Self, I::IntoIter>
    where
        I: IntoIterator<Item = Self::Item>,
        Self::Item: Mul<Output = Self::Item>,
    {
        VectorHadamard {
            iter1: self,
            iter2: other.into_iter(),
        }
    }

    fn scale<T>(self, scalar: T) -> VectorScale<Self, T>
    where
        T: Copy + Mul<Self::Item, Output = Self::Item>,
    {
        VectorScale { iter: self, scalar }
    }
}

pub fn mat_mul_l<'a, T>(vector: &'a [T], matrix: &'a [Vec<T>]) -> MatMulL<'a, T>
where
    T: Field + Zero,
{
    MatMulL {
        vector,
        matrix,
        column_index: 0,
    }
}

pub fn mat_mul_r<'a, T>(matrix: &'a [Vec<T>], vector: &'a [T]) -> MatMulR<'a, T>
where
    T: Field + Zero,
{
    MatMulR {
        matrix,
        vector,
        row_index: 0,
    }
}

pub fn hadarmard<T>(a: &[T], b: &[T]) -> Vec<T>
where
    T: Field,
{
    assert_eq!(a.len(), b.len(), "Hadamard product dimension mismatch");
    a.iter().zip(b.iter()).map(|(x, y)| *x * *y).collect()
}

impl<I: Iterator> VectorOps for I {}

pub fn inner_product<I1, I2, T>(a: I1, b: I2) -> T
where
    I1: IntoIterator,
    I2: IntoIterator,
    I1::Item: std::borrow::Borrow<T>,
    I2::Item: std::borrow::Borrow<T>,
    T: Field + Zero,
{
    a.into_iter()
        .zip(b)
        .map(|(x, y)| *x.borrow() * *y.borrow())
        .fold(T::zero(), |acc, x| acc + x)
}

pub fn sum<I, T>(iter: I) -> T
where
    I: IntoIterator<Item = T>,
    T: Field + Zero,
{
    iter.into_iter().fold(T::zero(), |acc, x| acc + x)
}

pub struct MatMulL<'a, T> {
    vector: &'a [T],
    matrix: &'a [Vec<T>],
    column_index: usize,
}

pub struct MatMulR<'a, T> {
    matrix: &'a [Vec<T>],
    vector: &'a [T],
    row_index: usize,
}

impl<T> Iterator for MatMulL<'_, T>
where
    T: Field + Zero,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.column_index >= self.matrix.first()?.len() {
            return None;
        }

        let result = inner_product(
            self.vector.iter(),
            self.matrix.iter().map(|row| row[self.column_index]),
        );
        self.column_index += 1;
        Some(result)
    }
}

impl<T> Iterator for MatMulR<'_, T>
where
    T: Field + Zero,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let row = self.matrix.get(self.row_index)?;
        assert_eq!(
            row.len(),
            self.vector.len(),
            "Matrix multiplication dimension mismatch"
        );

        let result = inner_product(row.iter(), self.vector.iter());
        self.row_index += 1;
        Some(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_secp256k1::Fr;

    #[test]
    fn test_vector_add() {
        let v1 = vec![1, 2, 3].into_iter().map(Fr::from).collect::<Vec<_>>();
        let v2 = vec![4, 5, 6].into_iter().map(Fr::from).collect::<Vec<_>>();
        let result: Vec<Fr> = v1.into_iter().vector_add(v2).collect();
        assert_eq!(
            result,
            vec![5, 7, 9].into_iter().map(Fr::from).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_scale() {
        let v = vec![1, 2, 3];
        let result: Vec<i32> = v.into_iter().scale(2).collect();
        assert_eq!(result, vec![2, 4, 6]);
    }

    #[test]
    fn test_inner_product() {
        let v1 = vec![1, 2, 3].into_iter().map(Fr::from).collect::<Vec<_>>();
        let v2 = vec![4, 5, 6].into_iter().map(Fr::from).collect::<Vec<_>>();
        let result = inner_product(v1, v2);
        assert_eq!(result, Fr::from(32)); // 1*4 + 2*5 + 3*6 = 4 + 10 + 18 = 32
    }

    #[test]
    fn test_composed_operations() {
        let v1 = vec![1, 2, 3].into_iter().map(Fr::from).collect::<Vec<_>>();
        let v2 = vec![2, 3, 4].into_iter().map(Fr::from).collect::<Vec<_>>();
        let v3 = vec![1, 1, 1].into_iter().map(Fr::from).collect::<Vec<_>>();
        let c = Fr::from(5);

        // inner_product(v1 + v2, scale(v3, c))
        let result = inner_product(v1.into_iter().vector_add(v2), v3.into_iter().scale(c));

        // v1 + v2 = [3, 5, 7]
        // scale(v3, 5) = [5, 5, 5]
        // inner_product = 3*5 + 5*5 + 7*5 = 15 + 25 + 35 = 75
        assert_eq!(result, Fr::from(75));
    }

    #[test]
    fn test_mat_mul_l() {
        let vector = vec![2, 3].into_iter().map(Fr::from).collect::<Vec<_>>();
        let matrix = vec![vec![1, 4], vec![2, 5], vec![3, 6]]
            .into_iter()
            .map(|v| v.into_iter().map(Fr::from).collect())
            .collect::<Vec<_>>();

        let result: Vec<Fr> = mat_mul_l(&vector, &matrix).collect();

        // col 1: 2*1 + 3*2 = 2 + 6 = 8
        // col 2: 2*4 + 3*5 = 8 + 15 = 23
        assert_eq!(
            result,
            vec![8, 23].into_iter().map(Fr::from).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_mat_mul_r() {
        let matrix = vec![vec![1, 2, 3], vec![4, 5, 6]]
            .into_iter()
            .map(|v| v.into_iter().map(Fr::from).collect())
            .collect::<Vec<_>>();
        let vector = vec![1, 2, 3].into_iter().map(Fr::from).collect::<Vec<_>>();

        let result: Vec<Fr> = mat_mul_r(&matrix, &vector).collect();

        // row 1: 1*1 + 2*2 + 3*3 = 1 + 4 + 9 = 14
        // row 2: 4*1 + 5*2 + 6*3 = 4 + 10 + 18 = 32
        assert_eq!(
            result,
            vec![14, 32].into_iter().map(Fr::from).collect::<Vec<_>>()
        );
    }
}
