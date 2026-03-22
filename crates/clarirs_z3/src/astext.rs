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
#[allow(clippy::approx_constant)]
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

impl<'c> AstExtZ3<'c> for AstRef<'c> {
    fn to_z3(&self) -> Result<RcAst, ClarirsError> {
        Z3_AST_CACHE.with(|cache| {
            walk_post_order(
                self.clone(),
                |node, children| to_z3_node(&node, children),
                cache,
            )
        })
    }

    fn from_z3(ctx: &'c Context<'c>, ast: impl Into<RcAst>) -> Result<Self, ClarirsError> {
        let ast = ast.into();
        // Try each type's from_z3 in order
        if let Ok(result) = bool::from_z3(ctx, ast.clone()) {
            return Ok(result);
        }
        if let Ok(result) = bv::from_z3(ctx, ast.clone()) {
            return Ok(result);
        }
        if let Ok(result) = float::from_z3(ctx, ast.clone()) {
            return Ok(result);
        }
        if let Ok(result) = string::from_z3(ctx, ast.clone()) {
            return Ok(result);
        }
        Err(ClarirsError::ConversionError(
            "Unknown AST type".to_string(),
        ))
    }
}

/// Check the Z3 sort of an RcAst to determine if it's a bitvector.
fn is_z3_bv(ast: &RcAst) -> bool {
    Z3_CONTEXT.with(|&z3_ctx| unsafe {
        let sort = z3::get_sort(z3_ctx, **ast);
        z3::get_sort_kind(z3_ctx, sort) == z3::SortKind::Bv
    })
}

fn to_z3_node(ast: &AstRef, children: &[RcAst]) -> Result<RcAst, ClarirsError> {
    match ast.op() {
        // Cross-sort ops: dispatch based on Z3 sort of children
        AstOp::Not(..) => {
            if !children.is_empty() && is_z3_bv(&children[0]) {
                bv::to_z3(ast, children)
            } else {
                bool::to_z3(ast, children)
            }
        }
        AstOp::And(..) | AstOp::Or(..) | AstOp::Xor(..) => {
            if !children.is_empty() && is_z3_bv(&children[0]) {
                bv::to_z3(ast, children)
            } else {
                bool::to_z3(ast, children)
            }
        }
        AstOp::If(..) => {
            // ITE: dispatch based on the sort of the "then" branch (children[1])
            if children.len() >= 2 && is_z3_bv(&children[1]) {
                bv::to_z3(ast, children)
            } else {
                // For bool/float/string ITE, the Z3 call is the same: mk_ite
                // Just use the common ITE handler
                Z3_CONTEXT.with(|&z3_ctx| unsafe {
                    let cond = child(children, 0)?;
                    let then = child(children, 1)?;
                    let else_ = child(children, 2)?;
                    let result = RcAst::try_from(z3::mk_ite(z3_ctx, **cond, **then, **else_))?;
                    crate::check_z3_error()?;
                    Ok(result)
                })
            }
        }

        // Eq/Neq always produce booleans
        AstOp::Eq(..) | AstOp::Neq(..) => bool::to_z3(ast, children),

        // Boolean-only leaf nodes and comparison ops
        AstOp::BoolS(..)
        | AstOp::BoolV(..)
        | AstOp::ULT(..)
        | AstOp::ULE(..)
        | AstOp::UGT(..)
        | AstOp::UGE(..)
        | AstOp::SLT(..)
        | AstOp::SLE(..)
        | AstOp::SGT(..)
        | AstOp::SGE(..)
        | AstOp::FpLt(..)
        | AstOp::FpLeq(..)
        | AstOp::FpGt(..)
        | AstOp::FpGeq(..)
        | AstOp::FpIsNan(..)
        | AstOp::FpIsInf(..)
        | AstOp::StrContains(..)
        | AstOp::StrPrefixOf(..)
        | AstOp::StrSuffixOf(..)
        | AstOp::StrIsDigit(..) => bool::to_z3(ast, children),

        // BitVec leaf nodes and ops
        AstOp::BVS(..)
        | AstOp::BVV(..)
        | AstOp::Neg(..)
        | AstOp::Add(..)
        | AstOp::Sub(..)
        | AstOp::Mul(..)
        | AstOp::UDiv(..)
        | AstOp::SDiv(..)
        | AstOp::URem(..)
        | AstOp::SRem(..)
        | AstOp::ShL(..)
        | AstOp::LShR(..)
        | AstOp::AShR(..)
        | AstOp::RotateLeft(..)
        | AstOp::RotateRight(..)
        | AstOp::ZeroExt(..)
        | AstOp::SignExt(..)
        | AstOp::Extract(..)
        | AstOp::Concat(..)
        | AstOp::ByteReverse(..)
        | AstOp::FpToIEEEBV(..)
        | AstOp::FpToUBV(..)
        | AstOp::FpToSBV(..)
        | AstOp::StrLen(..)
        | AstOp::StrIndexOf(..)
        | AstOp::StrToBV(..)
        | AstOp::Union(..)
        | AstOp::Intersection(..)
        | AstOp::Widen(..) => bv::to_z3(ast, children),

        // Float leaf nodes and ops
        AstOp::FPS(..)
        | AstOp::FPV(..)
        | AstOp::FpNeg(..)
        | AstOp::FpAbs(..)
        | AstOp::FpAdd(..)
        | AstOp::FpSub(..)
        | AstOp::FpMul(..)
        | AstOp::FpDiv(..)
        | AstOp::FpSqrt(..)
        | AstOp::FpToFp(..)
        | AstOp::FpFP(..)
        | AstOp::BvToFp(..)
        | AstOp::BvToFpSigned(..)
        | AstOp::BvToFpUnsigned(..) => float::to_z3(ast, children),

        // String leaf nodes and ops
        AstOp::StringS(..)
        | AstOp::StringV(..)
        | AstOp::StrConcat(..)
        | AstOp::StrSubstr(..)
        | AstOp::StrReplace(..)
        | AstOp::BVToStr(..) => string::to_z3(ast, children),
    }
}
