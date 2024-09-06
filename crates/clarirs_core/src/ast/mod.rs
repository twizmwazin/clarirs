pub mod annotation;
pub mod factory;
pub mod kind;
pub mod node;
pub mod op;

use std::collections::{HashMap, HashSet};

pub use annotation::Annotation;
pub use factory::AstFactory;
pub use kind::AstKind;
pub use node::{AstNode, AstRef};
pub use op::AstOp;

use crate::util::precomputed_hasher::PrecomputedHasherBuilder;

pub type AstSet<'c> = HashSet<AstRef<'c>, PrecomputedHasherBuilder>;
pub type AstMap<'c, T> = HashMap<AstRef<'c>, T, PrecomputedHasherBuilder>;

pub trait AstSetExt<'c> {
    fn new() -> Self;
}

impl AstSetExt<'_> for AstSet<'_> {
    fn new() -> Self {
        HashSet::with_hasher(PrecomputedHasherBuilder)
    }
}

pub trait AstMapExt<'c, T> {
    fn new() -> Self;
}

impl<T> AstMapExt<'_, T> for AstMap<'_, T> {
    fn new() -> Self {
        HashMap::with_hasher(PrecomputedHasherBuilder)
    }
}
