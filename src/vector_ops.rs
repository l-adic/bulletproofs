use rayon::prelude::*;
use std::iter::Iterator;

/// Zero-allocation vector operations using iterator-based design
/// 
/// This module provides composable vector arithmetic operations that avoid
/// intermediate allocations by working with iterators and only materializing
/// results when explicitly requested.

/// Iterator adapter for element-wise addition of two iterators
pub struct Add<I1, I2> {
    iter1: I1,
    iter2: I2,
}

/// Iterator adapter for element-wise subtraction of two iterators
pub struct Sub<I1, I2> {
    iter1: I1,
    iter2: I2,
}

impl<I1, I2> Iterator for Add<I1, I2>
where
    I1: Iterator,
    I2: Iterator,
    I1::Item: std::ops::Add<I2::Item>,
{
    type Item = <I1::Item as std::ops::Add<I2::Item>>::Output;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.iter1.next(), self.iter2.next()) {
            (Some(a), Some(b)) => Some(a + b),
            _ => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (min1, max1) = self.iter1.size_hint();
        let (min2, max2) = self.iter2.size_hint();
        (min1.min(min2), max1.zip(max2).map(|(a, b)| a.min(b)))
    }
}

impl<I1, I2> Iterator for Sub<I1, I2>
where
    I1: Iterator,
    I2: Iterator,
    I1::Item: std::ops::Sub<I2::Item>,
{
    type Item = <I1::Item as std::ops::Sub<I2::Item>>::Output;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.iter1.next(), self.iter2.next()) {
            (Some(a), Some(b)) => Some(a - b),
            _ => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (min1, max1) = self.iter1.size_hint();
        let (min2, max2) = self.iter2.size_hint();
        (min1.min(min2), max1.zip(max2).map(|(a, b)| a.min(b)))
    }
}

/// Iterator adapter for scalar multiplication
pub struct Scale<I, S> {
    iter: I,
    scalar: S,
}

impl<I, S> Iterator for Scale<I, S>
where
    I: Iterator,
    S: Clone,
    I::Item: std::ops::Mul<S>,
{
    type Item = <I::Item as std::ops::Mul<S>>::Output;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|x| x * self.scalar.clone())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// Iterator adapter for hadamard (element-wise) product
pub struct Hadamard<I1, I2> {
    iter1: I1,
    iter2: I2,
}

impl<I1, I2> Iterator for Hadamard<I1, I2>
where
    I1: Iterator,
    I2: Iterator,
    I1::Item: std::ops::Mul<I2::Item>,
{
    type Item = <I1::Item as std::ops::Mul<I2::Item>>::Output;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.iter1.next(), self.iter2.next()) {
            (Some(a), Some(b)) => Some(a * b),
            _ => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (min1, max1) = self.iter1.size_hint();
        let (min2, max2) = self.iter2.size_hint();
        (min1.min(min2), max1.zip(max2).map(|(a, b)| a.min(b)))
    }
}

/// Trait extending iterators with vector arithmetic operations
pub trait VectorOps: Iterator + Sized {
    /// Add this iterator element-wise with another
    fn add<I>(self, other: I) -> Add<Self, I::IntoIter>
    where
        I: IntoIterator,
        Self::Item: std::ops::Add<I::Item>,
    {
        Add {
            iter1: self,
            iter2: other.into_iter(),
        }
    }

    /// Subtract another iterator element-wise from this one
    fn sub<I>(self, other: I) -> Sub<Self, I::IntoIter>
    where
        I: IntoIterator,
        Self::Item: std::ops::Sub<I::Item>,
    {
        Sub {
            iter1: self,
            iter2: other.into_iter(),
        }
    }

    /// Multiply each element by a scalar
    fn scale<S>(self, scalar: S) -> Scale<Self, S>
    where
        Self::Item: std::ops::Mul<S>,
        S: Clone,
    {
        Scale { iter: self, scalar }
    }

    /// Element-wise multiplication with another iterator
    fn hadamard<I>(self, other: I) -> Hadamard<Self, I::IntoIter>
    where
        I: IntoIterator,
        Self::Item: std::ops::Mul<I::Item>,
    {
        Hadamard {
            iter1: self,
            iter2: other.into_iter(),
        }
    }

    /// Compute dot product (sum of hadamard product)
    fn dot<I>(self, other: I) -> Self::Item
    where
        I: IntoIterator,
        Self::Item: std::ops::Mul<I::Item> + std::iter::Sum<<Self::Item as std::ops::Mul<I::Item>>::Output>,
    {
        self.hadamard(other).sum()
    }

    /// Collect into a Vec with pre-allocated capacity if size is known
    fn collect_vec(self) -> Vec<Self::Item> {
        if let (_, Some(upper)) = self.size_hint() {
            let mut vec = Vec::with_capacity(upper);
            vec.extend(self);
            vec
        } else {
            self.collect()
        }
    }
}

// Implement VectorOps for all iterators
impl<I: Iterator> VectorOps for I {}

/// Trait for slice operations that automatically handle copying
pub trait SliceOps<T> {
    /// Zero-allocation hadamard product returning an iterator
    fn hadamard<'a, I>(&'a self, other: I) -> impl Iterator<Item = T> + 'a
    where
        I: IntoIterator<Item = T> + 'a,
        T: std::ops::Mul<Output = T> + Copy + 'a;

    /// Zero-allocation vector addition returning an iterator  
    fn add<'a, I>(&'a self, other: I) -> impl Iterator<Item = T> + 'a
    where
        I: IntoIterator<Item = T> + 'a,
        T: std::ops::Add<Output = T> + Copy + 'a;

    /// Zero-allocation vector subtraction returning an iterator
    fn sub<'a, I>(&'a self, other: I) -> impl Iterator<Item = T> + 'a
    where
        I: IntoIterator<Item = T> + 'a,
        T: std::ops::Sub<Output = T> + Copy + 'a;

    /// Zero-allocation scalar multiplication returning an iterator
    fn scale<'a>(&'a self, scalar: T) -> impl Iterator<Item = T> + 'a
    where
        T: std::ops::Mul<Output = T> + Copy + 'a;

    /// Zero-allocation dot product for slices
    fn dot<I>(&self, other: I) -> T
    where
        I: IntoIterator<Item = T>,
        T: std::ops::Mul<Output = T> + std::iter::Sum<T> + Copy;

    /// Combined scaling and addition: self * x + other * y
    fn scale_add<'a, I>(&'a self, x: T, other: I, y: T) -> impl Iterator<Item = T> + 'a
    where
        I: IntoIterator<Item = T> + 'a,
        T: std::ops::Mul<Output = T> + std::ops::Add<Output = T> + Copy + 'a;
}

impl<T> SliceOps<T> for [T] {
    fn hadamard<'a, I>(&'a self, other: I) -> impl Iterator<Item = T> + 'a
    where
        I: IntoIterator<Item = T> + 'a,
        T: std::ops::Mul<Output = T> + Copy + 'a,
    {
        self.iter().copied().hadamard(other)
    }

    fn add<'a, I>(&'a self, other: I) -> impl Iterator<Item = T> + 'a
    where
        I: IntoIterator<Item = T> + 'a,
        T: std::ops::Add<Output = T> + Copy + 'a,
    {
        self.iter().copied().add(other)
    }

    fn sub<'a, I>(&'a self, other: I) -> impl Iterator<Item = T> + 'a
    where
        I: IntoIterator<Item = T> + 'a,
        T: std::ops::Sub<Output = T> + Copy + 'a,
    {
        self.iter().copied().sub(other)
    }

    fn scale<'a>(&'a self, scalar: T) -> impl Iterator<Item = T> + 'a
    where
        T: std::ops::Mul<Output = T> + Copy + 'a,
    {
        self.iter().copied().scale(scalar)
    }

    fn dot<I>(&self, other: I) -> T
    where
        I: IntoIterator<Item = T>,
        T: std::ops::Mul<Output = T> + std::iter::Sum<T> + Copy,
    {
        self.iter().copied().dot(other)
    }

    fn scale_add<'a, I>(&'a self, x: T, other: I, y: T) -> impl Iterator<Item = T> + 'a
    where
        I: IntoIterator<Item = T> + 'a,
        T: std::ops::Mul<Output = T> + std::ops::Add<Output = T> + Copy + 'a,
    {
        self.iter().copied().scale(x).add(other.into_iter().scale(y))
    }
}

/// Convenience functions for common operations on slices (for backwards compatibility)
pub mod slice_ops {
    use super::*;
    use ark_ff::Field;

    /// Zero-allocation dot product for slices
    pub fn dot<F: Field>(a: &[F], b: &[F]) -> F {
        a.dot(b)
    }

    /// Zero-allocation hadamard product returning an iterator
    pub fn hadamard<'a, F>(a: &'a [F], b: &'a [F]) -> impl Iterator<Item = F> + 'a
    where
        F: std::ops::Mul<Output = F> + Copy,
    {
        a.hadamard(b)
    }

    /// Zero-allocation vector addition returning an iterator
    pub fn add<'a, F>(a: &'a [F], b: &'a [F]) -> impl Iterator<Item = F> + 'a
    where
        F: std::ops::Add<Output = F> + Copy,
    {
        a.add(b)
    }

    /// Zero-allocation vector subtraction returning an iterator
    pub fn sub<'a, F>(a: &'a [F], b: &'a [F]) -> impl Iterator<Item = F> + 'a
    where
        F: std::ops::Sub<Output = F> + Copy,
    {
        a.sub(b)
    }

    /// Zero-allocation scalar multiplication returning an iterator
    pub fn scale<F>(a: &[F], scalar: F) -> impl Iterator<Item = F> + '_
    where
        F: std::ops::Mul<Output = F> + Copy,
    {
        a.scale(scalar)
    }

    /// Combined scaling and addition: a * x + b * y
    pub fn scale_add<'a, F>(a: &'a [F], x: F, b: &'a [F], y: F) -> impl Iterator<Item = F> + 'a
    where
        F: std::ops::Mul<Output = F> + std::ops::Add<Output = F> + Copy,
    {
        a.scale_add(x, b, y)
    }

    /// Parallel versions using rayon
    pub mod parallel {
        use rayon::prelude::*;
        use ark_ff::Field;

        pub fn dot<F: Field + Send + Sync>(a: &[F], b: &[F]) -> F 
        where
            F: std::iter::Sum<F>,
        {
            a.par_iter().zip(b.par_iter()).map(|(x, y)| *x * *y).sum()
        }

        pub fn collect_hadamard<F>(a: &[F], b: &[F]) -> Vec<F>
        where
            F: std::ops::Mul<Output = F> + Copy + Send + Sync,
        {
            a.par_iter().zip(b.par_iter()).map(|(x, y)| *x * *y).collect()
        }

        pub fn collect_add<F>(a: &[F], b: &[F]) -> Vec<F>
        where
            F: std::ops::Add<Output = F> + Copy + Send + Sync,
        {
            a.par_iter().zip(b.par_iter()).map(|(x, y)| *x + *y).collect()
        }

        pub fn collect_sub<F>(a: &[F], b: &[F]) -> Vec<F>
        where
            F: std::ops::Sub<Output = F> + Copy + Send + Sync,
        {
            a.par_iter().zip(b.par_iter()).map(|(x, y)| *x - *y).collect()
        }

        pub fn collect_scale<F>(a: &[F], scalar: F) -> Vec<F>
        where
            F: std::ops::Mul<Output = F> + Copy + Send + Sync,
        {
            a.par_iter().map(|x| *x * scalar).collect()
        }

        pub fn collect_scale_add<F>(a: &[F], x: F, b: &[F], y: F) -> Vec<F>
        where
            F: std::ops::Mul<Output = F> + std::ops::Add<Output = F> + Copy + Send + Sync,
        {
            a.par_iter().zip(b.par_iter())
                .map(|(a_i, b_i)| *a_i * x + *b_i * y)
                .collect()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_secp256k1::Fr;
    use ark_ff::{Field, UniformRand, Zero, One};
    use proptest::prelude::*;

    // Property-based test generators
    prop_compose! {
        fn arb_field_vec(size: usize)
                       (values in prop::collection::vec(any::<u64>(), size))
                       -> Vec<Fr> {
            values.into_iter().map(Fr::from).collect()
        }
    }

    prop_compose! {
        fn arb_field_scalar()
                           (value in any::<u64>())
                           -> Fr {
            Fr::from(value)
        }
    }

    // Property tests
    proptest! {
        #[test]
        fn prop_dot_product_commutative(
            a in arb_field_vec(20),
            b in arb_field_vec(20)
        ) {
            let dot_ab = slice_ops::dot(&a, &b);
            let dot_ba = slice_ops::dot(&b, &a);
            prop_assert_eq!(dot_ab, dot_ba);
        }

        #[test]
        fn prop_dot_product_distributive(
            a in arb_field_vec(15),
            b in arb_field_vec(15),
            c in arb_field_vec(15)
        ) {
            // a · (b + c) = a · b + a · c
            let left = slice_ops::dot(&a, &slice_ops::add(&b, &c).collect_vec());
            let right = slice_ops::dot(&a, &b) + slice_ops::dot(&a, &c);
            prop_assert_eq!(left, right);
        }

        #[test]
        fn prop_scalar_multiplication_associative(
            a in arb_field_vec(12),
            s1 in arb_field_scalar(),
            s2 in arb_field_scalar()
        ) {
            // (s1 * s2) * a = s1 * (s2 * a)
            let left: Vec<_> = slice_ops::scale(&a, s1 * s2).collect();
            let right: Vec<_> = slice_ops::scale(&slice_ops::scale(&a, s2).collect_vec(), s1).collect();
            prop_assert_eq!(left, right);
        }

        #[test]
        fn prop_vector_addition_commutative(
            a in arb_field_vec(10),
            b in arb_field_vec(10)
        ) {
            let ab: Vec<_> = slice_ops::add(&a, &b).collect();
            let ba: Vec<_> = slice_ops::add(&b, &a).collect();
            prop_assert_eq!(ab, ba);
        }

        #[test]
        fn prop_vector_subtraction_anticommutative(
            a in arb_field_vec(10),
            b in arb_field_vec(10)
        ) {
            // a - b = -(b - a)
            let ab: Vec<_> = slice_ops::sub(&a, &b).collect();
            let ba: Vec<_> = slice_ops::sub(&b, &a).collect();
            let neg_ba: Vec<_> = ba.iter().map(|x| -*x).collect();
            prop_assert_eq!(ab, neg_ba);
        }

        #[test]
        fn prop_vector_addition_associative(
            a in arb_field_vec(8),
            b in arb_field_vec(8),
            c in arb_field_vec(8)
        ) {
            // (a + b) + c = a + (b + c)
            let left: Vec<_> = slice_ops::add(&slice_ops::add(&a, &b).collect_vec(), &c).collect();
            let right: Vec<_> = slice_ops::add(&a, &slice_ops::add(&b, &c).collect_vec()).collect();
            prop_assert_eq!(left, right);
        }

        #[test]
        fn prop_hadamard_commutative(
            a in arb_field_vec(10),
            b in arb_field_vec(10)
        ) {
            let ab: Vec<_> = slice_ops::hadamard(&a, &b).collect();
            let ba: Vec<_> = slice_ops::hadamard(&b, &a).collect();
            prop_assert_eq!(ab, ba);
        }

        #[test]
        fn prop_scalar_distributive_over_addition(
            a in arb_field_vec(10),
            b in arb_field_vec(10),
            s in arb_field_scalar()
        ) {
            // s * (a + b) = s * a + s * b
            let left: Vec<_> = slice_ops::scale(&slice_ops::add(&a, &b).collect_vec(), s).collect();
            let right: Vec<_> = slice_ops::add(&slice_ops::scale(&a, s).collect_vec(), 
                                              &slice_ops::scale(&b, s).collect_vec()).collect();
            prop_assert_eq!(left, right);
        }

        #[test]
        fn prop_dot_product_linearity_left(
            a in arb_field_vec(8),
            b in arb_field_vec(8),
            c in arb_field_vec(8),
            s in arb_field_scalar()
        ) {
            // (s * a + b) · c = s * (a · c) + b · c
            let scaled_a: Vec<_> = slice_ops::scale(&a, s).collect();
            let sum: Vec<_> = slice_ops::add(&scaled_a, &b).collect();
            let left = slice_ops::dot(&sum, &c);
            let right = s * slice_ops::dot(&a, &c) + slice_ops::dot(&b, &c);
            prop_assert_eq!(left, right);
        }

        #[test]
        fn prop_iterator_composition_matches_manual(
            a in arb_field_vec(6),
            b in arb_field_vec(6),
            c in arb_field_vec(6),
            s in arb_field_scalar()
        ) {
            // Test complex composition: hadamard(a, scale_add(b, s, c, s))
            let iter_result: Vec<_> = a.iter().copied()
                .hadamard(slice_ops::scale_add(&b, s, &c, s))
                .collect();
            
            let manual_result: Vec<_> = (0..a.len())
                .map(|i| a[i] * (b[i] * s + c[i] * s))
                .collect();
            
            prop_assert_eq!(iter_result, manual_result);
        }

        #[test]
        fn prop_zero_identity_addition(a in arb_field_vec(10)) {
            let zeros = vec![Fr::zero(); a.len()];
            let result: Vec<_> = slice_ops::add(&a, &zeros).collect();
            prop_assert_eq!(result, a);
        }

        #[test]
        fn prop_one_identity_hadamard(a in arb_field_vec(10)) {
            let ones = vec![Fr::one(); a.len()];
            let result: Vec<_> = slice_ops::hadamard(&a, &ones).collect();
            prop_assert_eq!(result, a);
        }

        #[test]
        fn prop_parallel_matches_sequential_dot(
            a in arb_field_vec(50),
            b in arb_field_vec(50)
        ) {
            let seq_result = slice_ops::dot(&a, &b);
            let par_result = slice_ops::parallel::dot(&a, &b);
            prop_assert_eq!(seq_result, par_result);
        }

        #[test]
        fn prop_parallel_matches_sequential_operations(
            a in arb_field_vec(30),
            b in arb_field_vec(30),
            s in arb_field_scalar()
        ) {
            // Test hadamard
            let seq_hadamard: Vec<_> = slice_ops::hadamard(&a, &b).collect();
            let par_hadamard = slice_ops::parallel::collect_hadamard(&a, &b);
            prop_assert_eq!(seq_hadamard, par_hadamard);

            // Test addition
            let seq_add: Vec<_> = slice_ops::add(&a, &b).collect();
            let par_add = slice_ops::parallel::collect_add(&a, &b);
            prop_assert_eq!(seq_add, par_add);

            // Test subtraction
            let seq_sub: Vec<_> = slice_ops::sub(&a, &b).collect();
            let par_sub = slice_ops::parallel::collect_sub(&a, &b);
            prop_assert_eq!(seq_sub, par_sub);

            // Test scaling
            let seq_scale: Vec<_> = slice_ops::scale(&a, s).collect();
            let par_scale = slice_ops::parallel::collect_scale(&a, s);
            prop_assert_eq!(seq_scale, par_scale);
        }
    }

    // Unit tests for edge cases and specific scenarios

    #[test]
    fn test_empty_vectors() {
        let empty_a: Vec<Fr> = vec![];
        let empty_b: Vec<Fr> = vec![];
        
        let dot_result = slice_ops::dot(&empty_a, &empty_b);
        assert_eq!(dot_result, Fr::zero());
        
        let hadamard_result: Vec<Fr> = slice_ops::hadamard(&empty_a, &empty_b).collect();
        assert!(hadamard_result.is_empty());
    }

    #[test]
    fn test_single_element_vectors() {
        let a = [Fr::from(5u64)];
        let b = [Fr::from(3u64)];
        
        let dot_result = slice_ops::dot(&a, &b);
        assert_eq!(dot_result, Fr::from(15u64));
        
        let hadamard_result: Vec<Fr> = slice_ops::hadamard(&a, &b).collect();
        assert_eq!(hadamard_result, vec![Fr::from(15u64)]);
    }

    #[test]
    fn test_size_hint_propagation() {
        let a = vec![1, 2, 3, 4, 5];
        let b = vec![6, 7, 8, 9, 10];
        
        let add_iter = a.iter().copied().add(b.iter().copied());
        let (min, max) = add_iter.size_hint();
        assert_eq!(min, 5);
        assert_eq!(max, Some(5));
        
        let scale_iter = a.iter().copied().scale(2);
        let (min, max) = scale_iter.size_hint();
        assert_eq!(min, 5);
        assert_eq!(max, Some(5));
    }

    #[test]
    fn test_iterator_composition_zero_allocations() {
        use ark_ff::UniformRand;
        let rng = &mut ark_std::test_rng();
        let a: Vec<Fr> = (0..1000).map(|_| Fr::rand(rng)).collect();
        let b: Vec<Fr> = (0..1000).map(|_| Fr::rand(rng)).collect();
        let c: Vec<Fr> = (0..1000).map(|_| Fr::rand(rng)).collect();
        let scalar = Fr::rand(rng);

        // Complex composition that would create many intermediate allocations
        // with naive implementation: hadamard(a, b + c * scalar)
        let iter_result: Vec<Fr> = a.iter().copied()
            .hadamard(b.iter().copied().add(c.iter().copied().scale(scalar)))
            .collect_vec();

        // Manual verification
        let manual_result: Vec<Fr> = (0..1000)
            .map(|i| a[i] * (b[i] + c[i] * scalar))
            .collect();

        assert_eq!(iter_result, manual_result);
    }

    #[test]
    fn test_mismatched_sizes() {
        let a = [Fr::from(1u64), Fr::from(2u64)];
        let b = [Fr::from(3u64), Fr::from(4u64), Fr::from(5u64)];
        
        // Should stop at the shorter length
        let result: Vec<Fr> = slice_ops::add(&a, &b).collect();
        assert_eq!(result.len(), 2);
        assert_eq!(result, vec![Fr::from(4u64), Fr::from(6u64)]);

        let sub_result: Vec<Fr> = slice_ops::sub(&a, &b).collect();
        assert_eq!(sub_result.len(), 2);
        assert_eq!(sub_result, vec![Fr::from(-2i64), Fr::from(-2i64)]);
    }

    #[test]
    fn test_subtraction_operations() {
        let a = [Fr::from(5u64), Fr::from(8u64), Fr::from(3u64)];
        let b = [Fr::from(2u64), Fr::from(3u64), Fr::from(1u64)];

        let sub_result: Vec<Fr> = slice_ops::sub(&a, &b).collect();
        assert_eq!(sub_result, vec![Fr::from(3u64), Fr::from(5u64), Fr::from(2u64)]);

        // Test with iterator composition: (a - b) * 2
        let composed_result: Vec<Fr> = slice_ops::sub(&a, &b).scale(Fr::from(2u64)).collect();
        assert_eq!(composed_result, vec![Fr::from(6u64), Fr::from(10u64), Fr::from(4u64)]);
    }
}