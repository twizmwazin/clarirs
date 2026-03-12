use std::collections::BTreeSet;
use std::fmt::Debug;
use std::hash::Hash;

use serde::Serialize;

use crate::prelude::*;

/// Generates a `Hash` impl for an Op enum. Each variant hashes a domain string,
/// a discriminant, and all its fields.
///
/// Syntax: `impl_op_hash!(OpType, "domain", Variant1(f1, f2) => disc1, ...)`
macro_rules! impl_op_hash {
    ($op:ident, $domain:expr, $( $Variant:ident( $($field:ident),* ) => $disc:expr ),* $(,)?) => {
        impl std::hash::Hash for $op<'_> {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                $domain.hash(state);
                match self {
                    $(
                        $op::$Variant( $($field),* ) => {
                            ($disc as u32).hash(state);
                            $( $field.hash(state); )*
                        }
                    )*
                }
            }
        }
    };
}

pub(crate) use impl_op_hash;

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

    fn symbolic(&self) -> bool {
        !self.variables().is_empty()
    }

    fn concrete(&self) -> bool {
        self.variables().is_empty()
    }

    fn check_same_sort(&self, other: &Self) -> bool;
}
