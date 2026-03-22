use crate::prelude::*;

use super::walk_post_order;

fn extract_child<'c>(children: &[AstRef<'c>], index: usize) -> Result<AstRef<'c>, ClarirsError> {
    children
        .get(index)
        .cloned()
        .ok_or(ClarirsError::InvalidArguments(format!(
            "missing child at index {index}"
        )))
}

/// Determine the result theory of a cross-sort operation by looking at the first
/// child in the already-excavated children list. Falls back to BOOLEAN.
fn result_theory<'c>(children: &[AstRef<'c>]) -> Theories {
    children
        .first()
        .map(|c| c.op().base_theories())
        .unwrap_or(Theories::BOOLEAN)
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
            |node, children| match node.op() {
                // Leaf nodes - return as-is
                AstOp::BoolS(..) | AstOp::BoolV(..) => Ok(node.clone()),
                AstOp::BVS(..) | AstOp::BVV(..) => Ok(node.clone()),
                AstOp::FPS(..) | AstOp::FPV(..) => Ok(node.clone()),
                AstOp::StringS(..) | AstOp::StringV(..) => Ok(node.clone()),

                // Cross-sort ops: dispatch based on children's theory
                AstOp::Not(..) | AstOp::And(..) | AstOp::Or(..) | AstOp::Xor(..) => {
                    let theory = result_theory(children);
                    if theory == Theories::BITVEC {
                        bitvec::excavate_ite(&node, children)
                    } else {
                        bool::excavate_ite(&node, children)
                    }
                }

                // Eq/Neq always produce booleans
                AstOp::Eq(..) | AstOp::Neq(..) => bool::excavate_ite(&node, children),

                // BV comparisons produce booleans
                AstOp::ULT(..)
                | AstOp::ULE(..)
                | AstOp::UGT(..)
                | AstOp::UGE(..)
                | AstOp::SLT(..)
                | AstOp::SLE(..)
                | AstOp::SGT(..)
                | AstOp::SGE(..) => bool::excavate_ite(&node, children),

                // Float comparisons produce booleans
                AstOp::FpLt(..)
                | AstOp::FpLeq(..)
                | AstOp::FpGt(..)
                | AstOp::FpGeq(..)
                | AstOp::FpIsNan(..)
                | AstOp::FpIsInf(..) => bool::excavate_ite(&node, children),

                // String comparisons produce booleans
                AstOp::StrContains(..)
                | AstOp::StrPrefixOf(..)
                | AstOp::StrSuffixOf(..)
                | AstOp::StrIsDigit(..) => bool::excavate_ite(&node, children),

                // BV arithmetic/bitwise
                AstOp::Neg(..)
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
                | AstOp::Widen(..) => bitvec::excavate_ite(&node, children),

                // Float operations
                AstOp::FpNeg(..)
                | AstOp::FpAbs(..)
                | AstOp::FpAdd(..)
                | AstOp::FpSub(..)
                | AstOp::FpMul(..)
                | AstOp::FpDiv(..)
                | AstOp::FpSqrt(..)
                | AstOp::FpToFp(..)
                | AstOp::BvToFp(..)
                | AstOp::BvToFpSigned(..)
                | AstOp::BvToFpUnsigned(..)
                | AstOp::FpFP(..) => float::excavate_ite(&node, children),

                // String operations
                AstOp::StrConcat(..)
                | AstOp::StrSubstr(..)
                | AstOp::StrReplace(..)
                | AstOp::BVToStr(..) => string::excavate_ite(&node, children),

                // If - just reconstruct with excavated children
                AstOp::If(..) => {
                    let cond = extract_child(children, 0)?;
                    let then_ = extract_child(children, 1)?;
                    let else_ = extract_child(children, 2)?;
                    Ok(node.context().ite(cond, then_, else_)?)
                }
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
