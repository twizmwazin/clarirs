use super::ReduceResult;
use crate::strided_interval::{ComparisonResult, StridedInterval};
use clarirs_core::prelude::*;

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

/// Reduce a BitVecAst to a StridedInterval
pub(crate) fn reduce_bv(
    ast: &BitVecAst<'_>,
    children: &[ReduceResult],
) -> Result<StridedInterval, ClarirsError> {
    Ok(match ast.op() {
        BitVecOp::BVS(_, bits) => {
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
        BitVecOp::BVV(bv) => StridedInterval::constant(bv.len(), bv.to_biguint()),
        BitVecOp::Not(..) => !child_si(children, 0)?,
        BitVecOp::And(..) => child_si(children, 0)? & child_si(children, 1)?,
        BitVecOp::Or(..) => child_si(children, 0)? | child_si(children, 1)?,
        BitVecOp::Xor(..) => child_si(children, 0)? ^ child_si(children, 1)?,
        BitVecOp::Neg(..) => -child_si(children, 0)?,
        BitVecOp::Add(..) => child_si(children, 0)? + child_si(children, 1)?,
        BitVecOp::Sub(..) => child_si(children, 0)? - child_si(children, 1)?,
        BitVecOp::Mul(..) => child_si(children, 0)? * child_si(children, 1)?,
        BitVecOp::UDiv(..) => child_si(children, 0)?.udiv(&child_si(children, 1)?)?,
        BitVecOp::SDiv(..) => child_si(children, 0)?.sdiv(&child_si(children, 1)?)?,
        BitVecOp::URem(..) => child_si(children, 0)?.urem(&child_si(children, 1)?)?,
        BitVecOp::SRem(..) => child_si(children, 0)?.srem(&child_si(children, 1)?)?,
        BitVecOp::ShL(..) => child_si(children, 0)?.shl(&child_si(children, 1)?)?,
        BitVecOp::LShR(..) => child_si(children, 0)?.lshr(&child_si(children, 1)?)?,
        BitVecOp::AShR(..) => child_si(children, 0)?.ashr(&child_si(children, 1)?)?,
        BitVecOp::RotateLeft(..) => child_si(children, 0)?.rotate_left(&child_si(children, 1)?)?,
        BitVecOp::RotateRight(..) => {
            child_si(children, 0)?.rotate_right(&child_si(children, 1)?)?
        }
        BitVecOp::ZeroExt(_, amount) => child_si(children, 0)?.zero_ext(*amount),
        BitVecOp::SignExt(_, amount) => child_si(children, 0)?.sign_ext(*amount),
        BitVecOp::Extract(_, high, low) => child_si(children, 0)?.extract(*high, *low),
        BitVecOp::Concat(args) => {
            // Fold over all children with concat
            let mut result = child_si(children, 0)?;
            for i in 1..args.len() {
                result = result.concat(&child_si(children, i)?);
            }
            result
        }
        BitVecOp::ByteReverse(..) => child_si(children, 0)?.reverse_bytes()?,
        BitVecOp::FpToIEEEBV(..) | BitVecOp::FpToUBV(..) | BitVecOp::FpToSBV(..) => {
            return Err(ClarirsError::UnsupportedOperation(
                "Floating point operations are not supported".to_string(),
            ));
        }
        BitVecOp::StrLen(..) | BitVecOp::StrIndexOf(..) | BitVecOp::StrToBV(..) => {
            return Err(ClarirsError::UnsupportedOperation(
                "String operations are not supported".to_string(),
            ));
        }
        BitVecOp::ITE(..) => match child(children, 0)? {
            ComparisonResult::True => child_si(children, 1)?,
            ComparisonResult::False => child_si(children, 2)?,
            ComparisonResult::Maybe => child_si(children, 1)?.union(&child_si(children, 2)?),
        },
        BitVecOp::Union(..) => child_si(children, 0)?.union(&child_si(children, 1)?),
        BitVecOp::Intersection(..) => child_si(children, 0)?.intersection(&child_si(children, 1)?),
        BitVecOp::Widen(..) => child_si(children, 0)?.widen(&child_si(children, 1)?),
    })
}
