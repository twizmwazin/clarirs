use clarirs_core::prelude::*;
use cvc5_rs::{Kind, RoundingMode, Term, TermManager};

use super::AstExtCvc5;

pub(crate) fn fprm_to_cvc5(tm: &TermManager, rm: FPRM) -> Term {
    tm.mk_rm(match rm {
        FPRM::NearestTiesToEven => RoundingMode::CVC5_RM_ROUND_NEAREST_TIES_TO_EVEN,
        FPRM::TowardPositive => RoundingMode::CVC5_RM_ROUND_TOWARD_POSITIVE,
        FPRM::TowardNegative => RoundingMode::CVC5_RM_ROUND_TOWARD_NEGATIVE,
        FPRM::TowardZero => RoundingMode::CVC5_RM_ROUND_TOWARD_ZERO,
        FPRM::NearestTiesToAway => RoundingMode::CVC5_RM_ROUND_NEAREST_TIES_TO_AWAY,
    })
}

fn parse_fprm_from_cvc5(term: &Term) -> Result<FPRM, ClarirsError> {
    let rm = term.rm_value();
    Ok(match rm {
        RoundingMode::CVC5_RM_ROUND_NEAREST_TIES_TO_EVEN => FPRM::NearestTiesToEven,
        RoundingMode::CVC5_RM_ROUND_TOWARD_POSITIVE => FPRM::TowardPositive,
        RoundingMode::CVC5_RM_ROUND_TOWARD_NEGATIVE => FPRM::TowardNegative,
        RoundingMode::CVC5_RM_ROUND_TOWARD_ZERO => FPRM::TowardZero,
        RoundingMode::CVC5_RM_ROUND_NEAREST_TIES_TO_AWAY => FPRM::NearestTiesToAway,
        _ => {
            return Err(ClarirsError::ConversionError(
                "Unknown rounding mode".to_string(),
            ))
        }
    })
}

pub(crate) fn to_cvc5(
    tm: &TermManager,
    ast: &FloatAst,
    children: &[Term],
) -> Result<Term, ClarirsError> {
    Ok(match ast.op() {
        FloatOp::FPS(s, sort) => {
            let cvc5_sort = tm.mk_fp_sort(sort.exponent, sort.mantissa + 1);
            tm.mk_const(cvc5_sort, s.as_str())
        }
        FloatOp::FPV(f) => {
            match f {
                Float::F32(val) => {
                    // Convert f32 to IEEE 754 bits and create from BV
                    let bits = val.to_bits();
                    let bv = tm.mk_bv_from_str(32, &bits.to_string(), 10);
                    let op = tm.mk_op(Kind::CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_IEEE_BV, &[8, 24]);
                    tm.mk_term_from_op(op, &[bv])
                }
                Float::F64(val) => {
                    let bits = val.to_bits();
                    let bv = tm.mk_bv_from_str(64, &bits.to_string(), 10);
                    let op = tm.mk_op(Kind::CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_IEEE_BV, &[11, 53]);
                    tm.mk_term_from_op(op, &[bv])
                }
            }
        }
        FloatOp::FpNeg(..) => {
            let a = children[0].clone();
            tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_NEG, &[a])
        }
        FloatOp::FpAbs(..) => {
            let a = children[0].clone();
            tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_ABS, &[a])
        }
        FloatOp::FpAdd(_, _, rm) => {
            let rm_term = fprm_to_cvc5(tm, *rm);
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_ADD, &[rm_term, a, b])
        }
        FloatOp::FpSub(_, _, rm) => {
            let rm_term = fprm_to_cvc5(tm, *rm);
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_SUB, &[rm_term, a, b])
        }
        FloatOp::FpMul(_, _, rm) => {
            let rm_term = fprm_to_cvc5(tm, *rm);
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_MULT, &[rm_term, a, b])
        }
        FloatOp::FpDiv(_, _, rm) => {
            let rm_term = fprm_to_cvc5(tm, *rm);
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_DIV, &[rm_term, a, b])
        }
        FloatOp::FpSqrt(_, rm) => {
            let rm_term = fprm_to_cvc5(tm, *rm);
            let a = children[0].clone();
            tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_SQRT, &[rm_term, a])
        }
        FloatOp::FpToFp(_, sort, rm) => {
            let rm_term = fprm_to_cvc5(tm, *rm);
            let a = children[0].clone();
            let op = tm.mk_op(
                Kind::CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_FP,
                &[sort.exponent, sort.mantissa + 1],
            );
            tm.mk_term_from_op(op, &[rm_term, a])
        }
        FloatOp::FpFP(..) => {
            let sign = children[0].clone();
            let exp = children[1].clone();
            let sig = children[2].clone();
            tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_FP, &[sign, exp, sig])
        }
        FloatOp::BvToFp(_, sort) => {
            let a = children[0].clone();
            let op = tm.mk_op(
                Kind::CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_IEEE_BV,
                &[sort.exponent, sort.mantissa + 1],
            );
            tm.mk_term_from_op(op, &[a])
        }
        FloatOp::BvToFpSigned(_, sort, rm) => {
            let rm_term = fprm_to_cvc5(tm, *rm);
            let a = children[0].clone();
            let op = tm.mk_op(
                Kind::CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_SBV,
                &[sort.exponent, sort.mantissa + 1],
            );
            tm.mk_term_from_op(op, &[rm_term, a])
        }
        FloatOp::BvToFpUnsigned(_, sort, rm) => {
            let rm_term = fprm_to_cvc5(tm, *rm);
            let a = children[0].clone();
            let op = tm.mk_op(
                Kind::CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_UBV,
                &[sort.exponent, sort.mantissa + 1],
            );
            tm.mk_term_from_op(op, &[rm_term, a])
        }
        FloatOp::ITE(..) => {
            let cond = children[0].clone();
            let then = children[1].clone();
            let else_ = children[2].clone();
            tm.mk_term(Kind::CVC5_KIND_ITE, &[cond, then, else_])
        }
    })
}

pub(crate) fn from_cvc5<'c>(
    ctx: &'c Context<'c>,
    tm: &TermManager,
    term: &Term,
) -> Result<FloatAst<'c>, ClarirsError> {
    let sort = term.sort();
    if !sort.is_fp() {
        return Err(ClarirsError::ConversionError(
            "expected a floating-point term".to_string(),
        ));
    }

    let ebits = sort.fp_exponent_size();
    let sbits = sort.fp_significand_size();
    let fsort = FSort::new(ebits, sbits - 1);
    let kind = term.kind();

    match kind {
        Kind::CVC5_KIND_CONST_FLOATINGPOINT => {
            // Extract float value
            let (_exp_width, _sig_width, bv_term) = term.fp_value();
            // Convert to f32 or f64
            if fsort == FSort::f32() {
                let bv_str = bv_term.bv_value(10);
                let bits: u32 = bv_str.parse().map_err(|_| {
                    ClarirsError::ConversionError("Failed to parse f32 bits".to_string())
                })?;
                ctx.fpv(Float::F32(f32::from_bits(bits)))
            } else if fsort == FSort::f64() {
                let bv_str = bv_term.bv_value(10);
                let bits: u64 = bv_str.parse().map_err(|_| {
                    ClarirsError::ConversionError("Failed to parse f64 bits".to_string())
                })?;
                ctx.fpv(Float::F64(f64::from_bits(bits)))
            } else {
                // Fallback: use f64
                let bv_str = bv_term.bv_value(10);
                let bits: u64 = bv_str.parse().map_err(|_| {
                    ClarirsError::ConversionError("Failed to parse float bits".to_string())
                })?;
                ctx.fpv(Float::F64(f64::from_bits(bits)))
            }
        }
        Kind::CVC5_KIND_CONSTANT => {
            let name = term.symbol();
            ctx.fps(name, fsort)
        }
        Kind::CVC5_KIND_FLOATINGPOINT_NEG => {
            let inner = FloatAst::from_cvc5(ctx, tm, &term.child(0))?;
            ctx.fp_neg(inner)
        }
        Kind::CVC5_KIND_FLOATINGPOINT_ABS => {
            let inner = FloatAst::from_cvc5(ctx, tm, &term.child(0))?;
            ctx.fp_abs(inner)
        }
        Kind::CVC5_KIND_FLOATINGPOINT_ADD
        | Kind::CVC5_KIND_FLOATINGPOINT_SUB
        | Kind::CVC5_KIND_FLOATINGPOINT_MULT
        | Kind::CVC5_KIND_FLOATINGPOINT_DIV => {
            let rm = parse_fprm_from_cvc5(&term.child(0))?;
            let a = FloatAst::from_cvc5(ctx, tm, &term.child(1))?;
            let b = FloatAst::from_cvc5(ctx, tm, &term.child(2))?;
            match kind {
                Kind::CVC5_KIND_FLOATINGPOINT_ADD => ctx.fp_add(a, b, rm),
                Kind::CVC5_KIND_FLOATINGPOINT_SUB => ctx.fp_sub(a, b, rm),
                Kind::CVC5_KIND_FLOATINGPOINT_MULT => ctx.fp_mul(a, b, rm),
                Kind::CVC5_KIND_FLOATINGPOINT_DIV => ctx.fp_div(a, b, rm),
                _ => unreachable!(),
            }
        }
        Kind::CVC5_KIND_FLOATINGPOINT_SQRT => {
            let rm = parse_fprm_from_cvc5(&term.child(0))?;
            let inner = FloatAst::from_cvc5(ctx, tm, &term.child(1))?;
            ctx.fp_sqrt(inner, rm)
        }
        Kind::CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_FP => {
            let rm = parse_fprm_from_cvc5(&term.child(0))?;
            let fp = FloatAst::from_cvc5(ctx, tm, &term.child(1))?;
            ctx.fp_to_fp(fp, fsort, rm)
        }
        Kind::CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_IEEE_BV => {
            let bv = crate::astext::bv::from_cvc5(ctx, tm, &term.child(0))?;
            ctx.bv_to_fp(bv, fsort)
        }
        Kind::CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_SBV => {
            let rm = parse_fprm_from_cvc5(&term.child(0))?;
            let bv = crate::astext::bv::from_cvc5(ctx, tm, &term.child(1))?;
            ctx.bv_to_fp_signed(bv, fsort, rm)
        }
        Kind::CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_UBV => {
            let rm = parse_fprm_from_cvc5(&term.child(0))?;
            let bv = crate::astext::bv::from_cvc5(ctx, tm, &term.child(1))?;
            ctx.bv_to_fp_unsigned(bv, fsort, rm)
        }
        Kind::CVC5_KIND_FLOATINGPOINT_FP => {
            let sign_bv = crate::astext::bv::from_cvc5(ctx, tm, &term.child(0))?;
            let exp_bv = crate::astext::bv::from_cvc5(ctx, tm, &term.child(1))?;
            let sig_bv = crate::astext::bv::from_cvc5(ctx, tm, &term.child(2))?;
            ctx.fp_fp(sign_bv, exp_bv, sig_bv)
        }
        Kind::CVC5_KIND_ITE => {
            let cond = crate::astext::bool::from_cvc5(ctx, tm, &term.child(0))?;
            let then = FloatAst::from_cvc5(ctx, tm, &term.child(1))?;
            let else_ = FloatAst::from_cvc5(ctx, tm, &term.child(2))?;
            ctx.ite(cond, then, else_)
        }
        _ => Err(ClarirsError::ConversionError(format!(
            "Failed converting from cvc5: unknown kind for float: {:?}",
            kind
        ))),
    }
}
