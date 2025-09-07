use ark_ff::Zero;
use std::ops::{Add, Mul, Sub};

pub trait Field: Copy + Add<Output = Self> + Mul<Output = Self> {}

impl<T> Field for T where T: Copy + Add<Output = Self> + Mul<Output = Self> {}

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

impl<I: Iterator> VectorOps for I {}

pub fn inner_product<I1, I2, T>(a: I1, b: I2) -> T
where
    I1: IntoIterator<Item = T>,
    I2: IntoIterator<Item = T>,
    T: Field + Zero,
{
    a.into_iter()
        .zip(b)
        .map(|(x, y)| x * y)
        .fold(T::zero(), |acc, x| acc + x)
}

pub fn sum<I, T>(iter: I) -> T
where
    I: IntoIterator<Item = T>,
    T: Field + Zero,
{
    iter.into_iter().fold(T::zero(), |acc, x| acc + x)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vector_add() {
        let v1 = vec![1, 2, 3];
        let v2 = vec![4, 5, 6];
        let result: Vec<i32> = v1.into_iter().vector_add(v2).collect();
        assert_eq!(result, vec![5, 7, 9]);
    }

    #[test]
    fn test_scale() {
        let v = vec![1, 2, 3];
        let result: Vec<i32> = v.into_iter().scale(2).collect();
        assert_eq!(result, vec![2, 4, 6]);
    }

    #[test]
    fn test_inner_product() {
        let v1 = vec![1, 2, 3];
        let v2 = vec![4, 5, 6];
        let result = inner_product(v1, v2);
        assert_eq!(result, 32); // 1*4 + 2*5 + 3*6 = 4 + 10 + 18 = 32
    }

    #[test]
    fn test_composed_operations() {
        let v1 = vec![1, 2, 3];
        let v2 = vec![2, 3, 4];
        let v3 = vec![1, 1, 1];
        let c = 5;

        // inner_product(v1 + v2, scale(v3, c))
        let result = inner_product(v1.into_iter().vector_add(v2), v3.into_iter().scale(c));

        // v1 + v2 = [3, 5, 7]
        // scale(v3, 5) = [5, 5, 5]
        // inner_product = 3*5 + 5*5 + 7*5 = 15 + 25 + 35 = 75
        assert_eq!(result, 75);
    }
}
