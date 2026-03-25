use crate::StridedInterval;
use crate::strided_interval::ComparisonResult;
use clarirs_core::prelude::*;

use super::ReduceResult;

fn child(children: &[ReduceResult], index: usize) -> Result<ComparisonResult, ClarirsError> {
    if let Some(ReduceResult::Bool(result)) = children.get(index) {
        Ok(result.clone())
    } else {
        Err(ClarirsError::InvalidArguments(format!(
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
        Err(ClarirsError::InvalidArguments(format!(
            "Expected BitVec at index {}, found {:?}",
            index,
            children.get(index)
        )))
    }
}

pub(crate) fn reduce_bool(
    ast: &AstRef<'_>,
    children: &[ReduceResult],
) -> Result<ComparisonResult, ClarirsError> {
    Ok(match ast.op() {
        Op::BoolS(..) => ComparisonResult::Maybe,
        Op::BoolV(v) => {
            if *v {
                ComparisonResult::True
            } else {
                ComparisonResult::False
            }
        }
        Op::Not(..) => !child(children, 0)?,
        Op::And(..) => {
            let mut result = ComparisonResult::True;
            for c in children {
                if let ReduceResult::Bool(b) = c {
                    result = result & b.clone();
                } else {
                    return Err(ClarirsError::InvalidArguments("Expected Bool".to_string()));
                }
            }
            result
        }
        Op::Or(..) => {
            let mut result = ComparisonResult::False;
            for c in children {
                if let ReduceResult::Bool(b) = c {
                    result = result | b.clone();
                } else {
                    return Err(ClarirsError::InvalidArguments("Expected Bool".to_string()));
                }
            }
            result
        }
        Op::Xor(..) => child(children, 0)? ^ child(children, 1)?,
        Op::BoolEq(..) => child(children, 0)?.eq_(child(children, 1)?),
        Op::BoolNeq(..) => !child(children, 0)?.eq_(child(children, 1)?),
        Op::Eq(..) => child_si(children, 0)?.eq_(&child_si(children, 1)?),
        Op::Neq(..) => child_si(children, 0)?.ne_(&child_si(children, 1)?),
        Op::ULT(..) => child_si(children, 0)?.ult(&child_si(children, 1)?),
        Op::ULE(..) => child_si(children, 0)?.ule(&child_si(children, 1)?),
        Op::UGT(..) => child_si(children, 0)?.ugt(&child_si(children, 1)?),
        Op::UGE(..) => child_si(children, 0)?.uge(&child_si(children, 1)?),
        Op::SLT(..) => child_si(children, 0)?.slt(&child_si(children, 1)?),
        Op::SLE(..) => child_si(children, 0)?.sle(&child_si(children, 1)?),
        Op::SGT(..) => child_si(children, 0)?.sgt(&child_si(children, 1)?),
        Op::SGE(..) => child_si(children, 0)?.sge(&child_si(children, 1)?),
        Op::FpEq(..)
        | Op::FpNeq(..)
        | Op::FpLt(..)
        | Op::FpLeq(..)
        | Op::FpGt(..)
        | Op::FpGeq(..)
        | Op::FpIsNan(..)
        | Op::FpIsInf(..) => {
            return Err(ClarirsError::UnsupportedOperation(
                "Floating point operations are not supported".to_string(),
            ));
        }
        Op::StrContains(..)
        | Op::StrPrefixOf(..)
        | Op::StrSuffixOf(..)
        | Op::StrIsDigit(..)
        | Op::StrEq(..)
        | Op::StrNeq(..) => {
            return Err(ClarirsError::UnsupportedOperation(
                "String operations are not supported".to_string(),
            ));
        }
        Op::ITE(..) => match child(children, 0)? {
            ComparisonResult::True => child(children, 1)?,
            ComparisonResult::False => child(children, 2)?,
            ComparisonResult::Maybe => child(children, 1)? | child(children, 2)?,
        },
        _ => {
            return Err(ClarirsError::UnsupportedOperation(
                "Unsupported operation for boolean reduction".to_string(),
            ));
        }
    })
}
