fn child(children: &[RcAst], index: usize) -> Result<&RcAst, ClarirsError> {
    children
        .get(index)
        .ok_or(ClarirsError::InvalidArguments(format!(
            "missing child at index {index}"
        )))
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

macro_rules! naryop {
    ($z3:ident, $children:ident, $op:ident) => {{
        let mut result = crate::astext::child($children, 0)?.clone();
        for i in 1..$children.len() {
            let b = crate::astext::child($children, i)?;
            result = RcAst::try_from(z3::$op($z3, *result, **b))?;
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
use clarirs_z3_sys as z3;

use crate::{Z3_AST_CACHE, Z3_CONTEXT, rc::RcAst};

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

impl<'c> AstExtZ3<'c> for DynAst<'c> {
    fn to_z3(&self) -> Result<RcAst, ClarirsError> {
        Z3_AST_CACHE.with(|cache| {
            walk_post_order(
                self.clone(),
                |node, children| match node.ty() {
                    AstType::Bool => bool::to_z3(&node, children),
                    AstType::BitVec(_) => bv::to_z3(&node, children),
                    AstType::Float(_) => float::to_z3(&node, children),
                    AstType::String => string::to_z3(&node, children),
                },
                cache,
            )
        })
    }

    fn from_z3(ctx: &'c Context<'c>, ast: impl Into<RcAst>) -> Result<Self, ClarirsError> {
        // The single AST type means there is one conversion entry point; we
        // determine the sort by trying each backend converter in turn.
        let ast = ast.into();
        if let Ok(a) = bool::from_z3(ctx, ast.clone()) {
            return Ok(a);
        }
        if let Ok(a) = bv::from_z3(ctx, ast.clone()) {
            return Ok(a);
        }
        if let Ok(a) = float::from_z3(ctx, ast.clone()) {
            return Ok(a);
        }
        if let Ok(a) = string::from_z3(ctx, ast.clone()) {
            return Ok(a);
        }
        Err(ClarirsError::ConversionError(
            "Unknown AST type".to_string(),
        ))
    }
}
