use rand::Rng;
use rand::seq::SliceRandom;
use std::collections::VecDeque;

pub struct BoundedProofQueue<T> {
    queue: VecDeque<T>,
    max_size: usize,
}

impl<T> BoundedProofQueue<T> {
    pub fn new(max_size: usize) -> Self {
        Self {
            queue: VecDeque::with_capacity(max_size),
            max_size,
        }
    }

    pub fn push(&mut self, item: T) {
        if self.queue.len() >= self.max_size {
            self.queue.pop_front(); // Remove oldest
        }
        self.queue.push_back(item);
    }

    pub fn choose<R: Rng + ?Sized>(&self, rng: &mut R) -> Option<&T> {
        self.queue
            .as_slices()
            .0
            .choose(rng)
            .or_else(|| self.queue.as_slices().1.choose(rng))
    }

    #[allow(dead_code)]
    pub fn choose_multiple<R: Rng + ?Sized>(&self, rng: &mut R, amount: usize) -> Vec<&T> {
        let items: Vec<&T> = self.queue.iter().collect();
        items.choose_multiple(rng, amount).copied().collect()
    }
}
