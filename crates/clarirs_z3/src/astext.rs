fn child(children: &[z3::Ast], index: usize) -> Result<&z3::Ast, ClarirsError> {
    children
        .get(index)
        .ok_or(ClarirsError::InvalidArguments(format!(
            "missing child at index {index}"
        )))
}

macro_rules! unop {
    ($z3:ident, $children:ident, $op:ident) => {{
        let a = crate::astext::child($children, 0)?;
        crate::checked_ast(z3::$op($z3, *a))?
    }};
}

macro_rules! binop {
    ($z3:ident, $children:ident, $op:ident) => {{
        let a = crate::astext::child($children, 0)?;
        let b = crate::astext::child($children, 1)?;
        crate::checked_ast(z3::$op($z3, *a, *b))?
    }};
}

macro_rules! naryop {
    ($z3:ident, $children:ident, $op:ident) => {{
        let mut result = *crate::astext::child($children, 0)?;
        for i in 1..$children.len() {
            let b = crate::astext::child($children, i)?;
            result = crate::checked_ast(z3::$op($z3, result, *b))?;
        }
        result
    }};
}

mod bool;
mod bv;
mod float;
mod string;

#[cfg(test)]
mod test_bool;
#[cfg(test)]
mod test_bv;
#[cfg(test)]
mod test_float;
#[cfg(test)]
mod test_string;

use clarirs_core::{algorithms::walk_post_order, prelude::*};
use crate::z3_compat as z3;

use crate::{Z3_AST_CACHE, Z3_CONTEXT, checked_ast};

pub(crate) trait AstExtZ3<'c>: HasContext<'c> + Simplify<'c> + Sized {
    fn to_z3(&self) -> Result<z3::Ast, ClarirsError>;
    fn from_z3(ctx: &'c Context<'c>, ast: z3::Ast) -> Result<Self, ClarirsError>;

    fn simplify_z3(&self) -> Result<Self, ClarirsError> {
        let ast = self.simplify()?.to_z3()?;
        Z3_CONTEXT.with(|ctx| unsafe {
            let simplified_ast = checked_ast(z3::simplify(*ctx, ast))?;
            Self::from_z3(self.context(), simplified_ast)
        })
    }
}

impl<'c> AstExtZ3<'c> for BoolAst<'c> {
    fn to_z3(&self) -> Result<z3::Ast, ClarirsError> {
        DynAst::from(self).to_z3()
    }

    fn from_z3(ctx: &'c Context<'c>, ast: z3::Ast) -> Result<Self, ClarirsError> {
        bool::from_z3(ctx, ast)
    }
}

impl<'c> AstExtZ3<'c> for BitVecAst<'c> {
    fn to_z3(&self) -> Result<z3::Ast, ClarirsError> {
        DynAst::from(self).to_z3()
    }

    fn from_z3(ctx: &'c Context<'c>, ast: z3::Ast) -> Result<Self, ClarirsError> {
        bv::from_z3(ctx, ast)
    }
}

impl<'c> AstExtZ3<'c> for FloatAst<'c> {
    fn to_z3(&self) -> Result<z3::Ast, ClarirsError> {
        DynAst::from(self).to_z3()
    }

    fn from_z3(ctx: &'c Context<'c>, ast: z3::Ast) -> Result<Self, ClarirsError> {
        float::from_z3(ctx, ast)
    }
}

impl<'c> AstExtZ3<'c> for StringAst<'c> {
    fn to_z3(&self) -> Result<z3::Ast, ClarirsError> {
        DynAst::from(self).to_z3()
    }

    fn from_z3(ctx: &'c Context<'c>, ast: z3::Ast) -> Result<Self, ClarirsError> {
        string::from_z3(ctx, ast)
    }
}

impl<'c> AstExtZ3<'c> for DynAst<'c> {
    fn to_z3(&self) -> Result<z3::Ast, ClarirsError> {
        Z3_AST_CACHE.with(|cache| {
            walk_post_order(
                self.clone(),
                |node, children| match node {
                    DynAst::Boolean(ast) => bool::to_z3(&ast, children),
                    DynAst::BitVec(ast) => bv::to_z3(&ast, children),
                    DynAst::Float(ast) => float::to_z3(&ast, children),
                    DynAst::String(ast) => string::to_z3(&ast, children),
                },
                cache,
            )
        })
    }

    fn from_z3(ctx: &'c Context<'c>, ast: z3::Ast) -> Result<Self, ClarirsError> {
        if let Ok(ast) = BoolAst::from_z3(ctx, ast) {
            return Ok(DynAst::Boolean(ast));
        }
        if let Ok(ast) = BitVecAst::from_z3(ctx, ast) {
            return Ok(DynAst::BitVec(ast));
        }
        if let Ok(ast) = FloatAst::from_z3(ctx, ast) {
            return Ok(DynAst::Float(ast));
        }
        if let Ok(ast) = StringAst::from_z3(ctx, ast) {
            return Ok(DynAst::String(ast));
        }
        Err(ClarirsError::ConversionError(
            "Unknown AST type".to_string(),
        ))
    }
}
