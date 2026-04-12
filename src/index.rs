use std::{fmt::Debug, hash::Hash, marker::PhantomData};

/// A trait to be implemented by any "index-like" types
pub trait Index: Copy + 'static + Eq + PartialEq + Debug + Hash {
    fn new(idx: usize) -> Self;

    fn index(self) -> usize;

    #[inline]
    fn increment_by(&mut self, amount: usize) {
        *self = self.plus(amount);
    }

    #[inline]
    #[must_use = "Use `increment_by` if you wanted to update the index in-place"]
    fn plus(self, amount: usize) -> Self {
        Self::new(self.index() + amount)
    }
}

pub macro simple_index($(#[$attr:meta])* $vis:vis struct $name:ident;) {
    $(#[$attr])*
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
    $vis struct $name(u32);

    impl $crate::index::Index for $name {
        fn new(idx: usize) -> Self {
            Self(idx as _)
        }

        fn index(self) -> usize {
            self.0 as _
        }
    }
}

pub struct IndexVec<I: Index, T> {
    pub raw: Vec<T>,
    _marker: PhantomData<fn(&I)>,
}

impl<I: Index, T> IndexVec<I, T> {
    /// Constructs a new, empty `IndexVec<I, T>`.
    #[inline]
    pub const fn new() -> Self {
        IndexVec::from_raw(Vec::new())
    }

    /// Constructs a new `IndexVec<I, T>` from a `Vec<T>`.
    #[inline]
    pub const fn from_raw(raw: Vec<T>) -> Self {
        IndexVec {
            raw,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        IndexVec::from_raw(Vec::with_capacity(capacity))
    }

    /// Pushes an element to the array returning the index where it was pushed to.
    #[inline]
    pub fn push(&mut self, d: T) -> I {
        let idx = self.next_index();
        self.raw.push(d);
        idx
    }

    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        self.raw.pop()
    }

    #[inline]
    pub fn into_iter(self) -> std::vec::IntoIter<T> {
        self.raw.into_iter()
    }

    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.raw.iter()
    }

    pub fn indices(&self) -> impl Iterator<Item = I> {
        (0..self.len()).map(|n| I::new(n))
    }

    pub fn enumerate(&self) -> impl Iterator<Item = (I, &'_ T)> {
        self.raw.iter().enumerate().map(|(i, v)| (I::new(i), v))
    }

    #[inline]
    pub fn into_entries(self) -> impl Iterator<Item = (I, T)> {
        self.raw
            .into_iter()
            .enumerate()
            .map(|(i, v)| (I::new(i), v))
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.raw.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    /// Gives the next index that will be assigned when `push` is called.
    ///
    /// Manual bounds checks can be done using `idx < slice.next_index()`
    /// (as opposed to `idx.index() < slice.len()`).
    #[inline]
    pub fn next_index(&self) -> I {
        I::new(self.len())
    }

    #[inline]
    pub fn get(&self, index: I) -> Option<&T> {
        self.raw.get(index.index())
    }

    #[inline]
    pub fn get_mut(&mut self, index: I) -> Option<&mut T> {
        self.raw.get_mut(index.index())
    }

    #[inline]
    pub fn ensure_contains_elem(&mut self, elem: I, fill_value: impl FnMut() -> T) -> &mut T {
        let min_new_len = elem.index() + 1;
        if self.len() < min_new_len {
            self.raw.resize_with(min_new_len, fill_value);
        }

        &mut self[elem]
    }
}

impl<I: Index, T: Debug> Debug for IndexVec<I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.raw.iter()).finish()
    }
}

impl<I: Index, T> core::ops::Index<I> for IndexVec<I, T> {
    type Output = T;

    fn index(&self, index: I) -> &Self::Output {
        self.get(index).unwrap()
    }
}
impl<I: Index, T> core::ops::IndexMut<I> for IndexVec<I, T> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.get_mut(index).unwrap()
    }
}
