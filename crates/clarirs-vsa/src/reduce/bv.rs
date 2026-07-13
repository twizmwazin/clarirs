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

/// Reduce a AstRef to a StridedInterval
pub(crate) fn reduce_bv(
    ast: &AstRef<'_>,
    children: &[ReduceResult],
) -> Result<StridedInterval, ClarirsError> {
    Ok(match ast.op() {
        AstOp::BVS(_, bits) => {
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
        AstOp::BVV(bv) => StridedInterval::constant(bv.len(), bv.to_biguint()),
        AstOp::Not(..) => child_si(children, 0)?.bitnot(),
        AstOp::And(..) => child_si(children, 0)?.bitand(&child_si(children, 1)?),
        AstOp::Or(..) => child_si(children, 0)?.bitor(&child_si(children, 1)?),
        AstOp::Xor(..) => child_si(children, 0)?.bitxor(&child_si(children, 1)?),
        AstOp::Neg(..) => child_si(children, 0)?.neg(),
        AstOp::Add(..) => child_si(children, 0)?.add(&child_si(children, 1)?),
        AstOp::Sub(..) => child_si(children, 0)?.sub(&child_si(children, 1)?),
        AstOp::Mul(..) => child_si(children, 0)?.mul(&child_si(children, 1)?),
        AstOp::UDiv(..) => child_si(children, 0)?.udiv(&child_si(children, 1)?)?,
        AstOp::SDiv(..) => child_si(children, 0)?.sdiv(&child_si(children, 1)?)?,
        AstOp::URem(..) => child_si(children, 0)?.urem(&child_si(children, 1)?)?,
        AstOp::SRem(..) => child_si(children, 0)?.srem(&child_si(children, 1)?)?,
        AstOp::ShL(..) => child_si(children, 0)?.shl(&child_si(children, 1)?)?,
        AstOp::LShR(..) => child_si(children, 0)?.lshr(&child_si(children, 1)?)?,
        AstOp::AShR(..) => child_si(children, 0)?.ashr(&child_si(children, 1)?)?,
        AstOp::RotateLeft(..) => child_si(children, 0)?.rotate_left(&child_si(children, 1)?)?,
        AstOp::RotateRight(..) => child_si(children, 0)?.rotate_right(&child_si(children, 1)?)?,
        AstOp::ZeroExt(_, amount) => child_si(children, 0)?.zero_extend(*amount),
        AstOp::SignExt(_, amount) => child_si(children, 0)?.sign_extend(*amount),
        AstOp::Extract(_, high, low) => child_si(children, 0)?.extract(*high, *low),
        AstOp::Concat(args) => {
            // Fold over all children with concat
            let mut result = child_si(children, 0)?;
            for i in 1..args.len() {
                result = result.concat(&child_si(children, i)?);
            }
            result
        }
        AstOp::ByteReverse(..) => child_si(children, 0)?.reverse_bytes()?,
        AstOp::FpToIEEEBV(..) | AstOp::FpToUBV(..) | AstOp::FpToSBV(..) => {
            return Err(ClarirsError::UnsupportedOperation(
                "Floating point operations are not supported".to_string(),
            ));
        }
        AstOp::StrLen(..) | AstOp::StrIndexOf(..) | AstOp::StrToBV(..) => {
            return Err(ClarirsError::UnsupportedOperation(
                "String operations are not supported".to_string(),
            ));
        }
        AstOp::ITE(..) => match child(children, 0)? {
            ComparisonResult::True => child_si(children, 1)?,
            ComparisonResult::False => child_si(children, 2)?,
            ComparisonResult::Maybe => child_si(children, 1)?.union(&child_si(children, 2)?),
        },
        AstOp::Union(..) => child_si(children, 0)?.union(&child_si(children, 1)?),
        AstOp::Intersection(..) => child_si(children, 0)?.intersection(&child_si(children, 1)?),
        AstOp::Widen(..) => child_si(children, 0)?.widen(&child_si(children, 1)?),
        _ => unreachable!("non-bitvector op dispatched to reduce_bv"),
    })
}

#[cfg(test)]
mod tests {
    use crate::reduce::Reduce;
    use crate::strided_interval::StridedInterval;
    use clarirs_core::prelude::*;
    use num_bigint::BigUint;

    fn reduce(ast: &AstRef) -> StridedInterval {
        ast.reduce().unwrap().into_bv().unwrap()
    }

    fn bv<'c>(ctx: &'c Context<'c>, value: u64, bits: u32) -> AstRef<'c> {
        ctx.bvv(BitVec::from((value, bits))).unwrap()
    }

    fn si<'c>(ctx: &'c Context<'c>, bits: u32, stride: u32, lb: u32, ub: u32) -> AstRef<'c> {
        ctx.si(
            bits,
            BigUint::from(stride),
            BigUint::from(lb),
            BigUint::from(ub),
        )
        .unwrap()
    }

    #[test]
    fn test_bvv_reduces_to_constant() {
        let ctx = Context::new();
        assert_eq!(
            reduce(&bv(&ctx, 42, 32)),
            StridedInterval::constant(32, 42u32)
        );
    }

    #[test]
    fn test_unannotated_bvs_reduces_to_top() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();
        assert_eq!(reduce(&x), StridedInterval::top(32));
    }

    #[test]
    fn test_annotated_bvs_uses_si_annotation() {
        let ctx = Context::new();
        assert_eq!(
            reduce(&si(&ctx, 32, 2, 10, 20)),
            StridedInterval::new(32, 2u32, 10u32, 20u32)
        );
    }

    #[test]
    fn test_esi_annotation_reduces_to_empty() {
        let ctx = Context::new();
        let e = ctx.esi(32).unwrap();
        assert_eq!(reduce(&e), StridedInterval::empty(32));
    }

    #[test]
    fn test_bitwise_ops_on_constants() {
        let ctx = Context::new();
        let a = bv(&ctx, 0xF0, 8);
        let b = bv(&ctx, 0x3C, 8);
        assert_eq!(
            reduce(&ctx.not(&a).unwrap()),
            StridedInterval::constant(8, 0x0Fu32)
        );
        assert_eq!(
            reduce(&ctx.and2(&a, &b).unwrap()),
            StridedInterval::constant(8, 0x30u32)
        );
        assert_eq!(
            reduce(&ctx.or2(&a, &b).unwrap()),
            StridedInterval::constant(8, 0xFCu32)
        );
        assert_eq!(
            reduce(&ctx.xor2(&a, &b).unwrap()),
            StridedInterval::constant(8, 0xCCu32)
        );
    }

    #[test]
    fn test_arithmetic_ops_on_constants() {
        let ctx = Context::new();
        assert_eq!(
            reduce(&ctx.add(bv(&ctx, 10, 32), bv(&ctx, 20, 32)).unwrap()),
            StridedInterval::constant(32, 30u32)
        );
        // 10 - 20 wraps to 246 in 8 bits
        assert_eq!(
            reduce(&ctx.sub(bv(&ctx, 10, 8), bv(&ctx, 20, 8)).unwrap()),
            StridedInterval::constant(8, 246u32)
        );
        assert_eq!(
            reduce(&ctx.mul(bv(&ctx, 6, 8), bv(&ctx, 7, 8)).unwrap()),
            StridedInterval::constant(8, 42u32)
        );
        // -(5) == 251 in 8 bits
        assert_eq!(
            reduce(&ctx.neg(bv(&ctx, 5, 8)).unwrap()),
            StridedInterval::constant(8, 251u32)
        );
    }

    #[test]
    fn test_division_ops_on_constants() {
        let ctx = Context::new();
        assert_eq!(
            reduce(&ctx.udiv(bv(&ctx, 100, 8), bv(&ctx, 7, 8)).unwrap()),
            StridedInterval::constant(8, 14u32)
        );
        // -10 sdiv 3 == -3 == 253 in 8 bits (0xF6 == -10)
        assert_eq!(
            reduce(&ctx.sdiv(bv(&ctx, 0xF6, 8), bv(&ctx, 3, 8)).unwrap()),
            StridedInterval::constant(8, 253u32)
        );
        // NOTE: urem's constant/constant fast path only fires when the
        // dividend equals the divisor (it compares s_lb to o_lb instead of
        // checking both operands are singletons), so 10 urem 3 is
        // conservatively approximated as [0, 2] instead of exactly 1.
        // This documents the current behavior (suspected bug).
        assert_eq!(
            reduce(&ctx.urem(bv(&ctx, 10, 8), bv(&ctx, 3, 8)).unwrap()),
            StridedInterval::range(8, 0u32, 2u32)
        );
        // -10 srem 3 == -1 == 255 in 8 bits
        assert_eq!(
            reduce(&ctx.srem(bv(&ctx, 0xF6, 8), bv(&ctx, 3, 8)).unwrap()),
            StridedInterval::constant(8, 255u32)
        );
    }

    #[test]
    fn test_shift_ops_on_constants() {
        let ctx = Context::new();
        assert_eq!(
            reduce(&ctx.shl(bv(&ctx, 3, 8), bv(&ctx, 2, 8)).unwrap()),
            StridedInterval::constant(8, 12u32)
        );
        assert_eq!(
            reduce(&ctx.lshr(bv(&ctx, 0x80, 8), bv(&ctx, 4, 8)).unwrap()),
            StridedInterval::constant(8, 0x08u32)
        );
        // Arithmetic shift preserves the sign bit: 0x80 >> 4 == 0xF8
        assert_eq!(
            reduce(&ctx.ashr(bv(&ctx, 0x80, 8), bv(&ctx, 4, 8)).unwrap()),
            StridedInterval::constant(8, 0xF8u32)
        );
        assert_eq!(
            reduce(&ctx.rotate_left(bv(&ctx, 0x81, 8), bv(&ctx, 1, 8)).unwrap()),
            StridedInterval::constant(8, 0x03u32)
        );
        assert_eq!(
            reduce(
                &ctx.rotate_right(bv(&ctx, 0x81, 8), bv(&ctx, 1, 8))
                    .unwrap()
            ),
            StridedInterval::constant(8, 0xC0u32)
        );
    }

    #[test]
    fn test_extension_and_extract_ops() {
        let ctx = Context::new();
        assert_eq!(
            reduce(&ctx.zero_ext(bv(&ctx, 0xFF, 8), 8).unwrap()),
            StridedInterval::constant(16, 0xFFu32)
        );
        // Sign extension of a negative value fills the upper bits
        assert_eq!(
            reduce(&ctx.sign_ext(bv(&ctx, 0x80, 8), 8).unwrap()),
            StridedInterval::constant(16, 0xFF80u32)
        );
        assert_eq!(
            reduce(&ctx.extract(bv(&ctx, 0xAB, 8), 7, 4).unwrap()),
            StridedInterval::constant(4, 0xAu32)
        );
    }

    #[test]
    fn test_concat() {
        let ctx = Context::new();
        assert_eq!(
            reduce(&ctx.concat2(bv(&ctx, 0xA, 4), bv(&ctx, 0xB, 4)).unwrap()),
            StridedInterval::constant(8, 0xABu32)
        );
        // Three-way concat folds left to right
        assert_eq!(
            reduce(
                &ctx.concat([bv(&ctx, 0x1, 4), bv(&ctx, 0x2, 4), bv(&ctx, 0x3, 4)])
                    .unwrap()
            ),
            StridedInterval::constant(12, 0x123u32)
        );
    }

    #[test]
    fn test_byte_reverse() {
        let ctx = Context::new();
        assert_eq!(
            reduce(&ctx.byte_reverse(bv(&ctx, 0x1234, 16)).unwrap()),
            StridedInterval::constant(16, 0x3412u32)
        );
    }

    #[test]
    fn test_ite() {
        let ctx = Context::new();
        let t = ctx.boolv(true).unwrap();
        let f = ctx.boolv(false).unwrap();
        let c = ctx.bools("c").unwrap();
        let one = bv(&ctx, 1, 8);
        let three = bv(&ctx, 3, 8);

        assert_eq!(
            reduce(&ctx.ite(&t, &one, &three).unwrap()),
            StridedInterval::constant(8, 1u32)
        );
        assert_eq!(
            reduce(&ctx.ite(&f, &one, &three).unwrap()),
            StridedInterval::constant(8, 3u32)
        );
        // Unknown condition: union of both branches, stride is the distance
        assert_eq!(
            reduce(&ctx.ite(&c, &one, &three).unwrap()),
            StridedInterval::new(8, 2u32, 1u32, 3u32)
        );
    }

    #[test]
    fn test_vsa_set_ops() {
        let ctx = Context::new();

        // Union of the constants 1 and 3
        assert_eq!(
            reduce(&ctx.union(bv(&ctx, 1, 8), bv(&ctx, 3, 8)).unwrap()),
            StridedInterval::new(8, 2u32, 1u32, 3u32)
        );

        // Intersection of [10, 30] and [20, 40] is [20, 30]
        assert_eq!(
            reduce(
                &ctx.intersection(si(&ctx, 32, 1, 10, 30), si(&ctx, 32, 1, 20, 40))
                    .unwrap()
            ),
            StridedInterval::new(32, 1u32, 20u32, 30u32)
        );

        // Widening [10, 20] against [10, 30]: the upper bound grew, so it is
        // extrapolated to the unsigned maximum
        assert_eq!(
            reduce(
                &ctx.widen(si(&ctx, 32, 1, 10, 20), si(&ctx, 32, 1, 10, 30))
                    .unwrap()
            ),
            StridedInterval::new(32, 1u32, 10u32, 0xFFFFFFFFu32)
        );
    }

    #[test]
    fn test_nested_expression() {
        let ctx = Context::new();
        // (x + 10) - 10 where x = 1[0, 100] stays 1[0, 100]
        let x = si(&ctx, 32, 1, 0, 100);
        let expr = ctx
            .sub(ctx.add(&x, bv(&ctx, 10, 32)).unwrap(), bv(&ctx, 10, 32))
            .unwrap();
        assert_eq!(reduce(&expr), StridedInterval::new(32, 1u32, 0u32, 100u32));
    }

    #[test]
    fn test_add_range_and_constant() {
        let ctx = Context::new();
        let x = si(&ctx, 8, 2, 10, 20);
        assert_eq!(
            reduce(&ctx.add(&x, bv(&ctx, 5, 8)).unwrap()),
            StridedInterval::new(8, 2u32, 15u32, 25u32)
        );
    }
}
