use crate::prelude::*;

use super::walk_post_order;

fn extract_child<'c>(
    children: &[AstRef<'c>],
    index: usize,
) -> Result<AstRef<'c>, ClarirsError> {
    children
        .get(index)
        .cloned()
        .ok_or(ClarirsError::InvalidArguments(format!(
            "missing child at index {index}"
        )))
}

/// Trait for excavating if-then-else expressions to the top level of an AST.
///
/// This transformation takes an AST containing nested ITE expressions and returns
/// an equivalent AST where the ITE expressions have been "excavated" (moved up) to the top level.
///
/// For example, if we have an expression like: `a + (if cond then b else c)`
///
/// After excavation, it would become: `if cond then (a + b) else (a + c)``
pub trait ExcavateIte<'c>: Sized {
    /// Transforms the AST by moving ITE expressions to the top level.
    ///
    /// Returns a new AST that is semantically equivalent to the original,
    /// but with ITE expressions moved to the top level where possible.
    fn excavate_ite(&self) -> Result<Self, ClarirsError>;
}

impl<'c> ExcavateIte<'c> for AstRef<'c> {
    fn excavate_ite(&self) -> Result<Self, ClarirsError> {
        walk_post_order(
            self.clone(),
            |node, children| match node.return_type() {
                AstType::Bool => bool::excavate_ite(&node, children),
                AstType::BitVec(_) => bitvec::excavate_ite(&node, children),
                AstType::Float(_) => float::excavate_ite(&node, children),
                AstType::String => string::excavate_ite(&node, children),
            },
            &self.context().excavate_ite_cache,
        )
    }
}

mod bitvec;
mod bool;
mod float;
mod string;

#[cfg(test)]
mod tests;
