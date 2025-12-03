use std::collections::BTreeSet;
use std::fmt::Debug;
use std::hash::Hash;

use serde::Serialize;

use crate::prelude::*;

pub trait Op<'c>: Debug + Hash + Serialize + PartialEq {
    type ChildIter<'a>: Iterator<Item = DynAst<'c>> + ExactSizeIterator
    where
        Self: 'a;

    fn child_iter(&self) -> Self::ChildIter<'_>;

    fn get_child(&self, index: usize) -> Option<DynAst<'c>>;

    fn depth(&self) -> u32 {
        1 + self.child_iter().map(|c| c.depth()).max().unwrap_or(0)
    }

    fn is_leaf(&self) -> bool {
        self.child_iter().next().is_none()
    }

    fn is_true(&self) -> bool {
        false
    }

    fn is_false(&self) -> bool {
        false
    }

    fn variables(&self) -> BTreeSet<InternedString>;

    fn symbolic(&self) -> bool {
        !self.variables().is_empty()
    }

    fn concrete(&self) -> bool {
        self.variables().is_empty()
    }

    fn check_same_sort(&self, other: &Self) -> bool;
}
