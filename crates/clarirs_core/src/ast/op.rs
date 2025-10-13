use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;
use std::vec::IntoIter;

use serde::Serialize;

use crate::prelude::*;

pub trait Op<'c>: Debug + Hash + Serialize + PartialEq {
    fn child_iter(&self) -> IntoIter<DynAst<'c>>;

    fn children(&self) -> Vec<DynAst<'c>> {
        self.child_iter().collect()
    }

    fn depth(&self) -> u32 {
        1 + self.children().iter().map(|c| c.depth()).max().unwrap_or(0)
    }

    fn is_leaf(&self) -> bool {
        self.children().is_empty()
    }

    fn is_true(&self) -> bool {
        false
    }

    fn is_false(&self) -> bool {
        false
    }

    fn variables(&self) -> HashSet<String>;

    fn symbolic(&self) -> bool {
        !self.variables().is_empty()
    }

    fn concrete(&self) -> bool {
        self.variables().is_empty()
    }

    fn check_same_sort(&self, other: &Self) -> bool;
}
