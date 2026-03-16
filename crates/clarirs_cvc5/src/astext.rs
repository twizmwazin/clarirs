mod bool;
mod bv;
mod float;
mod string;

use clarirs_core::{algorithms::walk_post_order, prelude::*};
use cvc5_rs::{Term, TermManager};

pub(crate) trait AstExtCvc5<'c>: HasContext<'c> + Simplify<'c> + Sized {
    fn to_cvc5(&self, tm: &TermManager) -> Result<Term, ClarirsError>;
    fn from_cvc5(ctx: &'c Context<'c>, tm: &TermManager, term: &Term)
        -> Result<Self, ClarirsError>;
}

impl<'c> AstExtCvc5<'c> for BoolAst<'c> {
    fn to_cvc5(&self, tm: &TermManager) -> Result<Term, ClarirsError> {
        DynAst::from(self).to_cvc5(tm)
    }

    fn from_cvc5(
        ctx: &'c Context<'c>,
        tm: &TermManager,
        term: &Term,
    ) -> Result<Self, ClarirsError> {
        bool::from_cvc5(ctx, tm, term)
    }
}

impl<'c> AstExtCvc5<'c> for BitVecAst<'c> {
    fn to_cvc5(&self, tm: &TermManager) -> Result<Term, ClarirsError> {
        DynAst::from(self).to_cvc5(tm)
    }

    fn from_cvc5(
        ctx: &'c Context<'c>,
        tm: &TermManager,
        term: &Term,
    ) -> Result<Self, ClarirsError> {
        bv::from_cvc5(ctx, tm, term)
    }
}

impl<'c> AstExtCvc5<'c> for FloatAst<'c> {
    fn to_cvc5(&self, tm: &TermManager) -> Result<Term, ClarirsError> {
        DynAst::from(self).to_cvc5(tm)
    }

    fn from_cvc5(
        ctx: &'c Context<'c>,
        tm: &TermManager,
        term: &Term,
    ) -> Result<Self, ClarirsError> {
        float::from_cvc5(ctx, tm, term)
    }
}

impl<'c> AstExtCvc5<'c> for StringAst<'c> {
    fn to_cvc5(&self, tm: &TermManager) -> Result<Term, ClarirsError> {
        DynAst::from(self).to_cvc5(tm)
    }

    fn from_cvc5(
        ctx: &'c Context<'c>,
        tm: &TermManager,
        term: &Term,
    ) -> Result<Self, ClarirsError> {
        string::from_cvc5(ctx, tm, term)
    }
}

impl<'c> AstExtCvc5<'c> for DynAst<'c> {
    fn to_cvc5(&self, tm: &TermManager) -> Result<Term, ClarirsError> {
        walk_post_order(
            self.clone(),
            |node, children| match node {
                DynAst::Boolean(ast) => bool::to_cvc5(tm, &ast, children),
                DynAst::BitVec(ast) => bv::to_cvc5(tm, &ast, children),
                DynAst::Float(ast) => float::to_cvc5(tm, &ast, children),
                DynAst::String(ast) => string::to_cvc5(tm, &ast, children),
            },
            &(),
        )
    }

    fn from_cvc5(
        ctx: &'c Context<'c>,
        tm: &TermManager,
        term: &Term,
    ) -> Result<Self, ClarirsError> {
        // Try them all
        if let Ok(ast) = BoolAst::from_cvc5(ctx, tm, term) {
            return Ok(DynAst::Boolean(ast));
        }
        if let Ok(ast) = BitVecAst::from_cvc5(ctx, tm, term) {
            return Ok(DynAst::BitVec(ast));
        }
        if let Ok(ast) = FloatAst::from_cvc5(ctx, tm, term) {
            return Ok(DynAst::Float(ast));
        }
        if let Ok(ast) = StringAst::from_cvc5(ctx, tm, term) {
            return Ok(DynAst::String(ast));
        }
        Err(ClarirsError::ConversionError(
            "Unknown AST type".to_string(),
        ))
    }
}
