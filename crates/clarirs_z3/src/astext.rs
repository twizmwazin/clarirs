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
        // Determine the sort from Z3 and dispatch to the appropriate from_z3
        Z3_CONTEXT.with(|z3_ctx| unsafe {
            let sort = z3::get_sort(*z3_ctx, *ast);
            let sort_kind = z3::get_sort_kind(*z3_ctx, sort);
            match sort_kind {
                z3::SortKind::Bool => bool::from_z3(ctx, ast),
                z3::SortKind::Bv => bv::from_z3(ctx, ast),
                z3::SortKind::FloatingPoint => float::from_z3(ctx, ast),
                z3::SortKind::Seq => string::from_z3(ctx, ast),
                _ => Err(ClarirsError::ConversionError(
                    "Unknown Z3 sort kind".to_string(),
                )),
            }
        })
    }
}

fn to_z3_node(ast: &AstRef<'_>, children: &[RcAst]) -> Result<RcAst, ClarirsError> {
    match ast.op() {
        // Boolean ops
        Op::BoolS(..) | Op::BoolV(..) | Op::Not(..) | Op::And(..) | Op::Or(..)
        | Op::Xor(..) | Op::BoolEq(..) | Op::BoolNeq(..) | Op::ITE(..)
        | Op::Eq(..) | Op::Neq(..) | Op::ULT(..) | Op::ULE(..) | Op::UGT(..)
        | Op::UGE(..) | Op::SLT(..) | Op::SLE(..) | Op::SGT(..) | Op::SGE(..)
        | Op::FpEq(..) | Op::FpNeq(..) | Op::FpLt(..) | Op::FpLeq(..)
        | Op::FpGt(..) | Op::FpGeq(..) | Op::FpIsNan(..) | Op::FpIsInf(..)
        | Op::StrContains(..) | Op::StrPrefixOf(..) | Op::StrSuffixOf(..)
        | Op::StrIsDigit(..) | Op::StrEq(..) | Op::StrNeq(..) => {
            bool::to_z3(ast, children)
        }

        // BitVec ops
        Op::BVS(..) | Op::BVV(..) | Op::BVNot(..) | Op::Neg(..) | Op::BVAnd(..)
        | Op::BVOr(..) | Op::BVXor(..) | Op::Add(..) | Op::Sub(..) | Op::Mul(..)
        | Op::UDiv(..) | Op::SDiv(..) | Op::URem(..) | Op::SRem(..) | Op::ShL(..)
        | Op::LShR(..) | Op::AShR(..) | Op::RotateLeft(..) | Op::RotateRight(..)
        | Op::ZeroExt(..) | Op::SignExt(..) | Op::Extract(..) | Op::Concat(..)
        | Op::ByteReverse(..) | Op::ITE(..) | Op::FpToIEEEBV(..)
        | Op::FpToUBV(..) | Op::FpToSBV(..) | Op::StrLen(..) | Op::StrIndexOf(..)
        | Op::StrToBV(..) | Op::Union(..) | Op::Intersection(..) | Op::Widen(..) => {
            bv::to_z3(ast, children)
        }

        // Float ops
        Op::FPS(..) | Op::FPV(..) | Op::FpNeg(..) | Op::FpAbs(..) | Op::FpAdd(..)
        | Op::FpSub(..) | Op::FpMul(..) | Op::FpDiv(..) | Op::FpSqrt(..)
        | Op::FpToFp(..) | Op::FpFP(..) | Op::BvToFp(..) | Op::BvToFpSigned(..)
        | Op::BvToFpUnsigned(..) | Op::ITE(..) => {
            float::to_z3(ast, children)
        }

        // String ops
        Op::StringS(..) | Op::StringV(..) | Op::StrConcat(..) | Op::StrSubstr(..)
        | Op::StrReplace(..) | Op::BVToStr(..) | Op::ITE(..) => {
            string::to_z3(ast, children)
        }
    }
}
