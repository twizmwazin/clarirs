mod bool;
mod bv;

use crate::strided_interval::{ComparisonResult, StridedInterval};
use clarirs_core::algorithms::walk_post_order;
use clarirs_core::prelude::*;

// Define an enum to represent the result of reduction
#[derive(Debug, Clone)]
pub enum ReduceResult {
    BitVec(StridedInterval),
    Bool(ComparisonResult),
}

/// The Reduce trait transforms expressions into abstract domains:
/// - BitVec expressions are reduced to StridedIntervals
/// - Bool expressions are reduced to ComparisonResults
/// - Float and String expressions return errors
pub trait Reduce<'c>: Sized {
    type Result;

    fn reduce(&self) -> Result<Self::Result, ClarirsError>;
}

impl<'c> Reduce<'c> for AstRef<'c> {
    type Result = ReduceResult;

    fn reduce(&self) -> Result<Self::Result, ClarirsError> {
        walk_post_order(
            self.clone(),
            |node, children| match node.op() {
                // Boolean leaf/op nodes
                AstOp::BoolS(..)
                | AstOp::BoolV(..)
                | AstOp::Not(..)
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
                | AstOp::StrIsDigit(..) => {
                    bool::reduce_bool(&node, children).map(ReduceResult::Bool)
                }
                // BitVec leaf/op nodes
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
                | AstOp::Widen(..) => bv::reduce_bv(&node, children).map(ReduceResult::BitVec),
                // Polymorphic ops: dispatch based on what children produce
                AstOp::And(..) | AstOp::Or(..) | AstOp::Xor(..) => {
                    // Check first child to determine sort
                    if children
                        .first()
                        .is_some_and(|c| matches!(c, ReduceResult::Bool(..)))
                    {
                        bool::reduce_bool(&node, children).map(ReduceResult::Bool)
                    } else {
                        bv::reduce_bv(&node, children).map(ReduceResult::BitVec)
                    }
                }
                AstOp::Eq(..) | AstOp::Neq(..) => {
                    bool::reduce_bool(&node, children).map(ReduceResult::Bool)
                }
                AstOp::If(..) => {
                    // Check second child (the "then" branch) to determine result sort
                    if children
                        .get(1)
                        .is_some_and(|c| matches!(c, ReduceResult::Bool(..)))
                    {
                        bool::reduce_bool(&node, children).map(ReduceResult::Bool)
                    } else {
                        bv::reduce_bv(&node, children).map(ReduceResult::BitVec)
                    }
                }
                _ => Err(ClarirsError::UnsupportedOperation(
                    "Unsupported operation for reduction".to_string(),
                )),
            },
            &(),
        )
    }
}
