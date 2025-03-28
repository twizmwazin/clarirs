use crate::prelude::*;

use super::walk_post_order;

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

impl<'c> ExcavateIte<'c> for DynAst<'c> {
    fn excavate_ite(&self) -> Result<Self, ClarirsError> {
        walk_post_order(
            self.clone(),
            |node, children| match node {
                DynAst::Boolean(ast) => bool::excavate_ite(&ast, &children).map(DynAst::Boolean),
                DynAst::BitVec(ast) => bitvec::excavate_ite(&ast, &children).map(DynAst::BitVec),
                DynAst::Float(_) => todo!("Implement ite excavation for FloatAst"),
                DynAst::String(_) => todo!("Implement ite excavation for StringAst"),
            },
            &self.context().excavate_ite_cache,
        )
    }
}

impl<'c> ExcavateIte<'c> for BoolAst<'c> {
    fn excavate_ite(&self) -> Result<Self, ClarirsError> {
        DynAst::Boolean(self.clone())
            .excavate_ite()?
            .into_bool()
            .ok_or(ClarirsError::TypeError("Expected BoolAst".to_string()))
    }
}

impl<'c> ExcavateIte<'c> for BitVecAst<'c> {
    fn excavate_ite(&self) -> Result<Self, ClarirsError> {
        DynAst::BitVec(self.clone())
            .excavate_ite()?
            .into_bitvec()
            .ok_or(ClarirsError::TypeError("Expected BvAst".to_string()))
    }
}

impl<'c> ExcavateIte<'c> for FloatAst<'c> {
    fn excavate_ite(&self) -> Result<Self, ClarirsError> {
        DynAst::Float(self.clone())
            .excavate_ite()?
            .into_float()
            .ok_or(ClarirsError::TypeError("Expected FloatAst".to_string()))
    }
}

impl<'c> ExcavateIte<'c> for StringAst<'c> {
    fn excavate_ite(&self) -> Result<Self, ClarirsError> {
        DynAst::String(self.clone())
            .excavate_ite()?
            .into_string()
            .ok_or(ClarirsError::TypeError("Expected StringAst".to_string()))
    }
}

mod bitvec;
mod bool;

#[cfg(test)]
mod tests;
