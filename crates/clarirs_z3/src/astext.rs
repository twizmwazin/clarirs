fn child(children: &[RcAst], index: usize) -> Result<&RcAst, ClarirsError> {
    children.get(index).ok_or(ClarirsError::InvalidArguments)
}

macro_rules! unop {
    ($z3:ident, $children:ident, $op:ident) => {{
        let a = crate::astext::child($children, 0)?;
        RcAst::try_from(z3::$op($z3, **a))?
    }};
}

macro_rules! binop {
    ($z3:ident, $children:ident, $op:ident) => {{
        let a = crate::astext::child($children, 0)?;
        let b = crate::astext::child($children, 1)?;
        RcAst::try_from(z3::$op($z3, **a, **b))?
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
use clarirs_z3_sys as z3;

use crate::{Z3_CONTEXT, rc::RcAst};

pub(crate) trait AstExtZ3<'c>: HasContext<'c> + Simplify<'c> + Sized {
    fn to_z3(&self) -> Result<RcAst, ClarirsError>;
    fn from_z3(ctx: &'c Context<'c>, ast: impl Into<RcAst>) -> Result<Self, ClarirsError>;

    fn simplify_z3(&self) -> Result<Self, ClarirsError> {
        let ast = self.simplify()?.to_z3()?;
        Z3_CONTEXT.with(|ctx| unsafe {
            let simplified_ast = RcAst::try_from(z3::simplify(*ctx, *ast))?;
            Self::from_z3(self.context(), simplified_ast)
        })
    }
}

impl<'c> AstExtZ3<'c> for BoolAst<'c> {
    fn to_z3(&self) -> Result<RcAst, ClarirsError> {
        DynAst::from(self).to_z3()
    }

    fn from_z3(ctx: &'c Context<'c>, ast: impl Into<RcAst>) -> Result<Self, ClarirsError> {
        bool::from_z3(ctx, ast)
    }
}

impl<'c> AstExtZ3<'c> for BitVecAst<'c> {
    fn to_z3(&self) -> Result<RcAst, ClarirsError> {
        DynAst::from(self).to_z3()
    }

    fn from_z3(ctx: &'c Context<'c>, ast: impl Into<RcAst>) -> Result<Self, ClarirsError> {
        bv::from_z3(ctx, ast)
    }
}

impl<'c> AstExtZ3<'c> for FloatAst<'c> {
    fn to_z3(&self) -> Result<RcAst, ClarirsError> {
        DynAst::from(self).to_z3()
    }

    fn from_z3(ctx: &'c Context<'c>, ast: impl Into<RcAst>) -> Result<Self, ClarirsError> {
        float::from_z3(ctx, ast)
    }
}

impl<'c> AstExtZ3<'c> for StringAst<'c> {
    fn to_z3(&self) -> Result<RcAst, ClarirsError> {
        DynAst::from(self).to_z3()
    }

    fn from_z3(ctx: &'c Context<'c>, ast: impl Into<RcAst>) -> Result<Self, ClarirsError> {
        string::from_z3(ctx, ast)
    }
}

impl<'c> AstExtZ3<'c> for DynAst<'c> {
    fn to_z3(&self) -> Result<RcAst, ClarirsError> {
        walk_post_order(
            self.clone(),
            |node, children| match node {
                DynAst::Boolean(ast) => bool::to_z3(&ast, children),
                DynAst::BitVec(ast) => bv::to_z3(&ast, children),
                DynAst::Float(ast) => float::to_z3(&ast, children),
                DynAst::String(ast) => string::to_z3(&ast, children),
            },
            &(),
        )
    }

    fn from_z3(ctx: &'c Context<'c>, ast: impl Into<RcAst>) -> Result<Self, ClarirsError> {
        // You probably want to use the `from_z3` method of the specific type

        let ast = ast.into();
        // Just try them all
        if let Ok(ast) = BoolAst::from_z3(ctx, ast.clone()) {
            return Ok(DynAst::Boolean(ast));
        }
        if let Ok(ast) = BitVecAst::from_z3(ctx, ast.clone()) {
            return Ok(DynAst::BitVec(ast));
        }
        if let Ok(ast) = FloatAst::from_z3(ctx, ast.clone()) {
            return Ok(DynAst::Float(ast));
        }
        if let Ok(ast) = StringAst::from_z3(ctx, ast.clone()) {
            return Ok(DynAst::String(ast));
        }
        Err(ClarirsError::ConversionError(
            "Unknown AST type".to_string(),
        ))
    }
}
