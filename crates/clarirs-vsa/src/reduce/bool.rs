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
        AstOp::BoolS(..) => ComparisonResult::Maybe,
        AstOp::BoolV(v) => {
            if *v {
                ComparisonResult::True
            } else {
                ComparisonResult::False
            }
        }
        AstOp::Not(..) => !child(children, 0)?,
        AstOp::And(..) => {
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
        AstOp::Or(..) => {
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
        AstOp::Xor(..) => {
            let mut result = ComparisonResult::False;
            for c in children {
                if let ReduceResult::Bool(b) = c {
                    result = result ^ b.clone();
                } else {
                    return Err(ClarirsError::InvalidArguments("Expected Bool".to_string()));
                }
            }
            result
        }
        AstOp::Eq(a, _) => {
            if a.ast_type().is_bool() {
                child(children, 0)?.eq_(child(children, 1)?)
            } else {
                child_si(children, 0)?.eq_(&child_si(children, 1)?)
            }
        }
        AstOp::Neq(a, _) => {
            if a.ast_type().is_bool() {
                !child(children, 0)?.eq_(child(children, 1)?)
            } else {
                child_si(children, 0)?.ne_(&child_si(children, 1)?)
            }
        }
        AstOp::ULT(..) => child_si(children, 0)?.ult(&child_si(children, 1)?),
        AstOp::ULE(..) => child_si(children, 0)?.ule(&child_si(children, 1)?),
        AstOp::UGT(..) => child_si(children, 0)?.ugt(&child_si(children, 1)?),
        AstOp::UGE(..) => child_si(children, 0)?.uge(&child_si(children, 1)?),
        AstOp::SLT(..) => child_si(children, 0)?.slt(&child_si(children, 1)?),
        AstOp::SLE(..) => child_si(children, 0)?.sle(&child_si(children, 1)?),
        AstOp::SGT(..) => child_si(children, 0)?.sgt(&child_si(children, 1)?),
        AstOp::SGE(..) => child_si(children, 0)?.sge(&child_si(children, 1)?),
        AstOp::FpLt(..)
        | AstOp::FpLeq(..)
        | AstOp::FpGt(..)
        | AstOp::FpGeq(..)
        | AstOp::FpIsNan(..)
        | AstOp::FpIsInf(..) => {
            return Err(ClarirsError::UnsupportedOperation(
                "Floating point operations are not supported".to_string(),
            ));
        }
        AstOp::StrContains(..)
        | AstOp::StrPrefixOf(..)
        | AstOp::StrSuffixOf(..)
        | AstOp::StrIsDigit(..) => {
            return Err(ClarirsError::UnsupportedOperation(
                "String operations are not supported".to_string(),
            ));
        }
        AstOp::ITE(..) => match child(children, 0)? {
            ComparisonResult::True => child(children, 1)?,
            ComparisonResult::False => child(children, 2)?,
            ComparisonResult::Maybe => child(children, 1)? | child(children, 2)?,
        },
        _ => unreachable!("non-boolean op dispatched to reduce_bool"),
    })
}

#[cfg(test)]
mod tests {
    use crate::reduce::Reduce;
    use crate::strided_interval::ComparisonResult;
    use clarirs_core::prelude::*;
    use num_bigint::BigUint;

    fn reduce(ast: &AstRef) -> ComparisonResult {
        ast.reduce().unwrap().into_bool().unwrap()
    }

    fn bv<'c>(ctx: &'c Context<'c>, value: u64, bits: u32) -> AstRef<'c> {
        ctx.bvv(BitVec::from((value, bits))).unwrap()
    }

    #[test]
    fn test_bool_values_and_symbols() {
        let ctx = Context::new();
        assert_eq!(reduce(&ctx.boolv(true).unwrap()), ComparisonResult::True);
        assert_eq!(reduce(&ctx.boolv(false).unwrap()), ComparisonResult::False);
        assert_eq!(reduce(&ctx.bools("b").unwrap()), ComparisonResult::Maybe);
    }

    #[test]
    fn test_not() {
        let ctx = Context::new();
        let t = ctx.boolv(true).unwrap();
        let f = ctx.boolv(false).unwrap();
        let s = ctx.bools("b").unwrap();
        assert_eq!(reduce(&ctx.not(&t).unwrap()), ComparisonResult::False);
        assert_eq!(reduce(&ctx.not(&f).unwrap()), ComparisonResult::True);
        assert_eq!(reduce(&ctx.not(&s).unwrap()), ComparisonResult::Maybe);
    }

    #[test]
    fn test_and() {
        let ctx = Context::new();
        let t = ctx.boolv(true).unwrap();
        let f = ctx.boolv(false).unwrap();
        let s = ctx.bools("b").unwrap();
        assert_eq!(reduce(&ctx.and2(&t, &t).unwrap()), ComparisonResult::True);
        assert_eq!(reduce(&ctx.and2(&t, &f).unwrap()), ComparisonResult::False);
        // False dominates even an unknown operand
        assert_eq!(reduce(&ctx.and2(&f, &s).unwrap()), ComparisonResult::False);
        assert_eq!(reduce(&ctx.and2(&t, &s).unwrap()), ComparisonResult::Maybe);
    }

    #[test]
    fn test_or() {
        let ctx = Context::new();
        let t = ctx.boolv(true).unwrap();
        let f = ctx.boolv(false).unwrap();
        let s = ctx.bools("b").unwrap();
        assert_eq!(reduce(&ctx.or2(&f, &f).unwrap()), ComparisonResult::False);
        assert_eq!(reduce(&ctx.or2(&f, &t).unwrap()), ComparisonResult::True);
        // True dominates even an unknown operand
        assert_eq!(reduce(&ctx.or2(&t, &s).unwrap()), ComparisonResult::True);
        assert_eq!(reduce(&ctx.or2(&f, &s).unwrap()), ComparisonResult::Maybe);
    }

    #[test]
    fn test_xor() {
        let ctx = Context::new();
        let t = ctx.boolv(true).unwrap();
        let f = ctx.boolv(false).unwrap();
        let s = ctx.bools("b").unwrap();
        assert_eq!(reduce(&ctx.xor2(&t, &f).unwrap()), ComparisonResult::True);
        assert_eq!(reduce(&ctx.xor2(&t, &t).unwrap()), ComparisonResult::False);
        assert_eq!(reduce(&ctx.xor2(&f, &f).unwrap()), ComparisonResult::False);
        assert_eq!(reduce(&ctx.xor2(&t, &s).unwrap()), ComparisonResult::Maybe);
    }

    #[test]
    fn test_eq_neq_bool_operands() {
        let ctx = Context::new();
        let t = ctx.boolv(true).unwrap();
        let f = ctx.boolv(false).unwrap();
        let s = ctx.bools("b").unwrap();
        assert_eq!(reduce(&ctx.eq_(&t, &t).unwrap()), ComparisonResult::True);
        assert_eq!(reduce(&ctx.eq_(&t, &f).unwrap()), ComparisonResult::False);
        assert_eq!(reduce(&ctx.eq_(&t, &s).unwrap()), ComparisonResult::Maybe);
        assert_eq!(reduce(&ctx.neq(&t, &f).unwrap()), ComparisonResult::True);
        assert_eq!(reduce(&ctx.neq(&t, &t).unwrap()), ComparisonResult::False);
        assert_eq!(reduce(&ctx.neq(&t, &s).unwrap()), ComparisonResult::Maybe);
    }

    #[test]
    fn test_eq_neq_bv_operands() {
        let ctx = Context::new();
        let five = bv(&ctx, 5, 32);
        let six = bv(&ctx, 6, 32);
        // 0..=10 overlaps the constant 5 without being equal to it
        let range = ctx
            .si(
                32,
                BigUint::from(1u32),
                BigUint::from(0u32),
                BigUint::from(10u32),
            )
            .unwrap();

        assert_eq!(
            reduce(&ctx.eq_(&five, &five).unwrap()),
            ComparisonResult::True
        );
        assert_eq!(
            reduce(&ctx.eq_(&five, &six).unwrap()),
            ComparisonResult::False
        );
        assert_eq!(
            reduce(&ctx.eq_(&range, &five).unwrap()),
            ComparisonResult::Maybe
        );
        assert_eq!(
            reduce(&ctx.neq(&five, &six).unwrap()),
            ComparisonResult::True
        );
        assert_eq!(
            reduce(&ctx.neq(&five, &five).unwrap()),
            ComparisonResult::False
        );
        assert_eq!(
            reduce(&ctx.neq(&range, &five).unwrap()),
            ComparisonResult::Maybe
        );
    }

    #[test]
    fn test_unsigned_comparisons() {
        let ctx = Context::new();
        let five = bv(&ctx, 5, 32);
        let ten = bv(&ctx, 10, 32);
        let range = ctx
            .si(
                32,
                BigUint::from(1u32),
                BigUint::from(0u32),
                BigUint::from(10u32),
            )
            .unwrap();

        assert_eq!(
            reduce(&ctx.ult(&five, &ten).unwrap()),
            ComparisonResult::True
        );
        assert_eq!(
            reduce(&ctx.ult(&ten, &five).unwrap()),
            ComparisonResult::False
        );
        assert_eq!(
            reduce(&ctx.ult(&range, &five).unwrap()),
            ComparisonResult::Maybe
        );
        assert_eq!(
            reduce(&ctx.ule(&five, &five).unwrap()),
            ComparisonResult::True
        );
        assert_eq!(
            reduce(&ctx.ule(&ten, &five).unwrap()),
            ComparisonResult::False
        );
        assert_eq!(
            reduce(&ctx.ugt(&ten, &five).unwrap()),
            ComparisonResult::True
        );
        assert_eq!(
            reduce(&ctx.ugt(&five, &ten).unwrap()),
            ComparisonResult::False
        );
        assert_eq!(
            reduce(&ctx.uge(&five, &five).unwrap()),
            ComparisonResult::True
        );
        assert_eq!(
            reduce(&ctx.uge(&five, &ten).unwrap()),
            ComparisonResult::False
        );
    }

    #[test]
    fn test_signed_comparisons() {
        let ctx = Context::new();
        // 0xF6 == -10 as a signed 8-bit value
        let minus_ten = bv(&ctx, 0xF6, 8);
        let five = bv(&ctx, 5, 8);

        assert_eq!(
            reduce(&ctx.slt(&minus_ten, &five).unwrap()),
            ComparisonResult::True
        );
        assert_eq!(
            reduce(&ctx.slt(&five, &minus_ten).unwrap()),
            ComparisonResult::False
        );
        assert_eq!(
            reduce(&ctx.sle(&minus_ten, &minus_ten).unwrap()),
            ComparisonResult::True
        );
        assert_eq!(
            reduce(&ctx.sgt(&five, &minus_ten).unwrap()),
            ComparisonResult::True
        );
        assert_eq!(
            reduce(&ctx.sgt(&minus_ten, &five).unwrap()),
            ComparisonResult::False
        );
        assert_eq!(
            reduce(&ctx.sge(&five, &five).unwrap()),
            ComparisonResult::True
        );
        assert_eq!(
            reduce(&ctx.sge(&minus_ten, &five).unwrap()),
            ComparisonResult::False
        );
    }

    #[test]
    fn test_comparison_with_empty_si_is_false() {
        let ctx = Context::new();
        let empty = ctx.esi(8).unwrap();
        let five = bv(&ctx, 5, 8);
        assert_eq!(
            reduce(&ctx.ult(&empty, &five).unwrap()),
            ComparisonResult::False
        );
        assert_eq!(
            reduce(&ctx.eq_(&empty, &five).unwrap()),
            ComparisonResult::False
        );
    }

    #[test]
    fn test_ite_known_condition() {
        let ctx = Context::new();
        let t = ctx.boolv(true).unwrap();
        let f = ctx.boolv(false).unwrap();
        let s = ctx.bools("b").unwrap();

        // Condition true: takes the then-branch
        assert_eq!(
            reduce(&ctx.ite(&t, &f, &s).unwrap()),
            ComparisonResult::False
        );
        // Condition false: takes the else-branch
        assert_eq!(
            reduce(&ctx.ite(&f, &s, &t).unwrap()),
            ComparisonResult::True
        );
    }

    #[test]
    fn test_ite_unknown_condition() {
        let ctx = Context::new();
        let t = ctx.boolv(true).unwrap();
        let f = ctx.boolv(false).unwrap();
        let c = ctx.bools("c").unwrap();
        let d = ctx.bools("d").unwrap();

        // NOTE: with an unknown condition, the branches are joined with
        // BitOr, so ITE(maybe, true, false) currently reduces to True even
        // though the accurate join of True and False is Maybe. This test
        // documents the current behavior (suspected bug).
        assert_eq!(
            reduce(&ctx.ite(&c, &t, &f).unwrap()),
            ComparisonResult::True
        );

        // Maybe | False stays Maybe
        assert_eq!(
            reduce(&ctx.ite(&c, &d, &f).unwrap()),
            ComparisonResult::Maybe
        );
    }
}
