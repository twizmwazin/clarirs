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

    fn get_child(&self, index: usize) -> Option<DynAst<'c>> {
        self.child_iter().nth(index)
    }

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

    /// Returns true if the op is inherently symbolic regardless of whether it
    /// has variables. For example, VSA operations (Union, Intersection, Widen)
    /// are always symbolic because they represent abstract multi-valued results.
    /// The default implementation returns false.
    fn is_inherently_symbolic(&self) -> bool {
        false
    }

    fn symbolic(&self) -> bool {
        self.is_inherently_symbolic() || !self.variables().is_empty()
    }

    fn concrete(&self) -> bool {
        !self.symbolic()
    }

    fn check_same_sort(&self, other: &Self) -> bool;
}
