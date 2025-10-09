use crate::StridedInterval;
use crate::strided_interval::ComparisonResult;
use clarirs_core::prelude::*;

use super::ReduceResult;

fn child(children: &[ReduceResult], index: usize) -> Result<ComparisonResult, ClarirsError> {
    if let Some(ReduceResult::Bool(result)) = children.get(index) {
        Ok(result.clone())
    } else {
        Err(ClarirsError::InvalidArgumentsWithMessage(format!(
            "Expected Bool at index {}, found {:?}",
            index,
            children.get(index)
        )))
    }
}

fn child_si(children: &[ReduceResult], index: usize) -> Result<StridedInterval, ClarirsError> {
    if let Some(ReduceResult::BitVec(result)) = children.get(index) {
        Ok(result.clone())
    } else {
        Err(ClarirsError::InvalidArgumentsWithMessage(format!(
            "Expected BitVec at index {}, found {:?}",
            index,
            children.get(index)
        )))
    }
}

pub(crate) fn reduce_bool(
    ast: &BoolAst<'_>,
    children: &[ReduceResult],
) -> Result<ComparisonResult, ClarirsError> {
    Ok(match ast.op() {
        BooleanOp::BoolS(..) => ComparisonResult::Maybe,
        BooleanOp::BoolV(v) => {
            if *v {
                ComparisonResult::True
            } else {
                ComparisonResult::False
            }
        }
        BooleanOp::Not(..) => !child(children, 0)?,
        BooleanOp::And(..) => child(children, 0)? & child(children, 1)?,
        BooleanOp::Or(..) => child(children, 0)? | child(children, 1)?,
        BooleanOp::Xor(..) => child(children, 0)? ^ child(children, 1)?,
        BooleanOp::BoolEq(..) => child(children, 0)?.eq_(child(children, 1)?),
        BooleanOp::BoolNeq(..) => !child(children, 0)?.eq_(child(children, 1)?),
        BooleanOp::Eq(..) => child_si(children, 0)?.eq_(&child_si(children, 1)?),
        BooleanOp::Neq(..) => child_si(children, 0)?.ne_(&child_si(children, 1)?),
        BooleanOp::ULT(..) => child_si(children, 0)?.ult(&child_si(children, 1)?),
        BooleanOp::ULE(..) => child_si(children, 0)?.ule(&child_si(children, 1)?),
        BooleanOp::UGT(..) => child_si(children, 0)?.ugt(&child_si(children, 1)?),
        BooleanOp::UGE(..) => child_si(children, 0)?.uge(&child_si(children, 1)?),
        BooleanOp::SLT(..) => child_si(children, 0)?.slt(&child_si(children, 1)?),
        BooleanOp::SLE(..) => child_si(children, 0)?.sle(&child_si(children, 1)?),
        BooleanOp::SGT(..) => child_si(children, 0)?.sgt(&child_si(children, 1)?),
        BooleanOp::SGE(..) => child_si(children, 0)?.sge(&child_si(children, 1)?),
        BooleanOp::FpEq(..)
        | BooleanOp::FpNeq(..)
        | BooleanOp::FpLt(..)
        | BooleanOp::FpLeq(..)
        | BooleanOp::FpGt(..)
        | BooleanOp::FpGeq(..)
        | BooleanOp::FpIsNan(..)
        | BooleanOp::FpIsInf(..) => {
            return Err(ClarirsError::UnsupportedOperation(
                "Floating point operations are not supported".to_string(),
            ));
        }
        BooleanOp::StrContains(..)
        | BooleanOp::StrPrefixOf(..)
        | BooleanOp::StrSuffixOf(..)
        | BooleanOp::StrIsDigit(..)
        | BooleanOp::StrEq(..)
        | BooleanOp::StrNeq(..) => {
            return Err(ClarirsError::UnsupportedOperation(
                "String operations are not supported".to_string(),
            ));
        }
        BooleanOp::If(..) => match child(children, 0)? {
            ComparisonResult::True => child(children, 1)?,
            ComparisonResult::False => child(children, 2)?,
            ComparisonResult::Maybe => child(children, 1)? | child(children, 2)?,
        },
    })
}
