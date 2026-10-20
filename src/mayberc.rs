use std::fmt::Display;
use std::hash::Hash;
use std::{fmt::Debug, ops::Deref, rc::Rc};

#[derive(Clone)]
pub struct MaybeRc<T>(S<T>);
#[derive(Clone)]
enum S<T> {
    Rc(Rc<T>),
    Own(T),
}

impl<T: Clone> MaybeRc<T> {
    pub fn to_rc(self) -> Rc<T> {
        match self.0 {
            S::Rc(x) => x,
            S::Own(x) => Rc::new(x),
        }
    }
}

impl<T> Deref for MaybeRc<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        match &self.0 {
            S::Rc(x) => x,
            S::Own(x) => x,
        }
    }
}

impl<T: Eq> Eq for MaybeRc<T> {}
impl<T: PartialEq> PartialEq for MaybeRc<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        T::eq(self, other)
    }
}

impl<T: PartialOrd> PartialOrd for MaybeRc<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        T::partial_cmp(self, other)
    }
}

impl<T: Ord> Ord for MaybeRc<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        T::cmp(self, other)
    }
}

impl<T: Hash> Hash for MaybeRc<T> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        T::hash(self, state)
    }
}

impl<T> From<T> for MaybeRc<T> {
    #[inline]
    fn from(value: T) -> Self {
        Self(S::Own(value))
    }
}

impl<T> From<Rc<T>> for MaybeRc<T> {
    #[inline]
    fn from(value: Rc<T>) -> Self {
        Self(S::Rc(value))
    }
}

impl<T: Debug> Debug for MaybeRc<T> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        T::fmt(self, f)
    }
}

impl<T: Display> Display for MaybeRc<T> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        T::fmt(self, f)
    }
}
