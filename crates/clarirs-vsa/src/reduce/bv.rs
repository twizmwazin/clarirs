use super::ReduceResult;
use crate::strided_interval::{ComparisonResult, StridedInterval};
use clarirs_core::prelude::*;

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

/// Reduce a BitVec AST to a StridedInterval
pub(crate) fn reduce_bv(
    ast: &AstRef<'_>,
    children: &[ReduceResult],
) -> Result<StridedInterval, ClarirsError> {
    Ok(match ast.op() {
        Op::BVS(_, bits) => {
            // If there is an SI or ESI annotation, use it. Otherwise, return top.
            ast.annotations()
                .iter()
                .find_map(|ann| {
                    if let AnnotationType::StridedInterval {
                        stride,
                        lower_bound,
                        upper_bound,
                    } = ann.type_()
                    {
                        Some(StridedInterval::new(
                            *bits,
                            stride.clone(),
                            lower_bound.clone(),
                            upper_bound.clone(),
                        ))
                    } else if let AnnotationType::EmptyStridedInterval = ann.type_() {
                        Some(StridedInterval::empty(*bits))
                    } else {
                        None
                    }
                })
                .unwrap_or_else(|| StridedInterval::top(*bits))
        }
        Op::BVV(bv) => StridedInterval::constant(bv.len(), bv.to_biguint()),
        Op::BVNot(..) => child_si(children, 0)?.bitnot(),
        Op::BVAnd(args) => {
            let mut result = child_si(children, 0)?;
            for i in 1..args.len() {
                result = result.bitand(&child_si(children, i)?);
            }
            result
        }
        Op::BVOr(args) => {
            let mut result = child_si(children, 0)?;
            for i in 1..args.len() {
                result = result.bitor(&child_si(children, i)?);
            }
            result
        }
        Op::BVXor(args) => {
            let mut result = child_si(children, 0)?;
            for i in 1..args.len() {
                result = result.bitxor(&child_si(children, i)?);
            }
            result
        }
        Op::Neg(..) => child_si(children, 0)?.neg(),
        Op::Add(args) => {
            let mut result = child_si(children, 0)?;
            for i in 1..args.len() {
                result = result.add(&child_si(children, i)?);
            }
            result
        }
        Op::Sub(..) => child_si(children, 0)?.sub(&child_si(children, 1)?),
        Op::Mul(args) => {
            let mut result = child_si(children, 0)?;
            for i in 1..args.len() {
                result = result.mul(&child_si(children, i)?);
            }
            result
        }
        Op::UDiv(..) => child_si(children, 0)?.udiv(&child_si(children, 1)?)?,
        Op::SDiv(..) => child_si(children, 0)?.sdiv(&child_si(children, 1)?)?,
        Op::URem(..) => child_si(children, 0)?.urem(&child_si(children, 1)?)?,
        Op::SRem(..) => child_si(children, 0)?.srem(&child_si(children, 1)?)?,
        Op::ShL(..) => child_si(children, 0)?.shl(&child_si(children, 1)?)?,
        Op::LShR(..) => child_si(children, 0)?.lshr(&child_si(children, 1)?)?,
        Op::AShR(..) => child_si(children, 0)?.ashr(&child_si(children, 1)?)?,
        Op::RotateLeft(..) => child_si(children, 0)?.rotate_left(&child_si(children, 1)?)?,
        Op::RotateRight(..) => {
            child_si(children, 0)?.rotate_right(&child_si(children, 1)?)?
        }
        Op::ZeroExt(_, amount) => child_si(children, 0)?.zero_extend(*amount),
        Op::SignExt(_, amount) => child_si(children, 0)?.sign_extend(*amount),
        Op::Extract(_, high, low) => child_si(children, 0)?.extract(*high, *low),
        Op::Concat(args) => {
            // Fold over all children with concat
            let mut result = child_si(children, 0)?;
            for i in 1..args.len() {
                result = result.concat(&child_si(children, i)?);
            }
            result
        }
        Op::ByteReverse(..) => child_si(children, 0)?.reverse_bytes()?,
        Op::FpToIEEEBV(..) | Op::FpToUBV(..) | Op::FpToSBV(..) => {
            return Err(ClarirsError::UnsupportedOperation(
                "Floating point operations are not supported".to_string(),
            ));
        }
        Op::StrLen(..) | Op::StrIndexOf(..) | Op::StrToBV(..) => {
            return Err(ClarirsError::UnsupportedOperation(
                "String operations are not supported".to_string(),
            ));
        }
        Op::BVITE(..) => match child(children, 0)? {
            ComparisonResult::True => child_si(children, 1)?,
            ComparisonResult::False => child_si(children, 2)?,
            ComparisonResult::Maybe => child_si(children, 1)?.union(&child_si(children, 2)?),
        },
        Op::Union(..) => child_si(children, 0)?.union(&child_si(children, 1)?),
        Op::Intersection(..) => child_si(children, 0)?.intersection(&child_si(children, 1)?),
        Op::Widen(..) => child_si(children, 0)?.widen(&child_si(children, 1)?),
        _ => {
            return Err(ClarirsError::UnsupportedOperation(
                "Unsupported operation for bitvec reduction".to_string(),
            ));
        }
    })
}
