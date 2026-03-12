use super::{extract_bitvec_child, extract_bool_child, extract_float_child};
use crate::prelude::*;

pub(crate) fn excavate_ite<'c>(
    ast: &FloatAst<'c>,
    children: &[DynAst<'c>],
) -> Result<FloatAst<'c>, ClarirsError> {
    let ctx = ast.context();

    match ast.op() {
        FloatOp::FPS(..) | FloatOp::FPV(..) => Ok(ast.clone()),
        FloatOp::FpNeg(..) => {
            let inner = extract_float_child(children, 0)?;

            if let FloatOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.fp_neg(then_)?, ctx.fp_neg(else_)?)?)
            } else {
                Ok(ctx.fp_neg(inner)?)
            }
        }
        FloatOp::FpAbs(..) => {
            let inner = extract_float_child(children, 0)?;

            if let FloatOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.fp_abs(then_)?, ctx.fp_abs(else_)?)?)
            } else {
                Ok(ctx.fp_abs(inner)?)
            }
        }
        FloatOp::FpAdd(_, _, rm) => {
            let rm = *rm;
            let lhs = extract_float_child(children, 0)?;
            let rhs = extract_float_child(children, 1)?;

            if let FloatOp::ITE(cond, then_, else_) = lhs.op() {
                if let FloatOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_add(then_, rhs_then, rm)?,
                            ctx.fp_add(then_, rhs_else, rm)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_add(else_, rhs_then, rm)?,
                            ctx.fp_add(else_, rhs_else, rm)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(
                        cond,
                        ctx.fp_add(then_, &rhs, rm)?,
                        ctx.fp_add(else_, rhs, rm)?,
                    )?)
                }
            } else if let FloatOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_add(&lhs, then_, rm)?,
                    ctx.fp_add(lhs, else_, rm)?,
                )?)
            } else {
                Ok(ctx.fp_add(lhs, rhs, rm)?)
            }
        }
        FloatOp::FpSub(_, _, rm) => {
            let rm = *rm;
            let lhs = extract_float_child(children, 0)?;
            let rhs = extract_float_child(children, 1)?;

            if let FloatOp::ITE(cond, then_, else_) = lhs.op() {
                if let FloatOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_sub(then_, rhs_then, rm)?,
                            ctx.fp_sub(then_, rhs_else, rm)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_sub(else_, rhs_then, rm)?,
                            ctx.fp_sub(else_, rhs_else, rm)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(
                        cond,
                        ctx.fp_sub(then_, &rhs, rm)?,
                        ctx.fp_sub(else_, rhs, rm)?,
                    )?)
                }
            } else if let FloatOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_sub(&lhs, then_, rm)?,
                    ctx.fp_sub(lhs, else_, rm)?,
                )?)
            } else {
                Ok(ctx.fp_sub(lhs, rhs, rm)?)
            }
        }
        FloatOp::FpMul(_, _, rm) => {
            let rm = *rm;
            let lhs = extract_float_child(children, 0)?;
            let rhs = extract_float_child(children, 1)?;

            if let FloatOp::ITE(cond, then_, else_) = lhs.op() {
                if let FloatOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_mul(then_, rhs_then, rm)?,
                            ctx.fp_mul(then_, rhs_else, rm)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_mul(else_, rhs_then, rm)?,
                            ctx.fp_mul(else_, rhs_else, rm)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(
                        cond,
                        ctx.fp_mul(then_, &rhs, rm)?,
                        ctx.fp_mul(else_, rhs, rm)?,
                    )?)
                }
            } else if let FloatOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_mul(&lhs, then_, rm)?,
                    ctx.fp_mul(lhs, else_, rm)?,
                )?)
            } else {
                Ok(ctx.fp_mul(lhs, rhs, rm)?)
            }
        }
        FloatOp::FpDiv(_, _, rm) => {
            let rm = *rm;
            let lhs = extract_float_child(children, 0)?;
            let rhs = extract_float_child(children, 1)?;

            if let FloatOp::ITE(cond, then_, else_) = lhs.op() {
                if let FloatOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_div(then_, rhs_then, rm)?,
                            ctx.fp_div(then_, rhs_else, rm)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_div(else_, rhs_then, rm)?,
                            ctx.fp_div(else_, rhs_else, rm)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(
                        cond,
                        ctx.fp_div(then_, &rhs, rm)?,
                        ctx.fp_div(else_, rhs, rm)?,
                    )?)
                }
            } else if let FloatOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_div(&lhs, then_, rm)?,
                    ctx.fp_div(lhs, else_, rm)?,
                )?)
            } else {
                Ok(ctx.fp_div(lhs, rhs, rm)?)
            }
        }
        FloatOp::FpSqrt(_, rm) => {
            let rm = *rm;
            let inner = extract_float_child(children, 0)?;

            if let FloatOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.fp_sqrt(then_, rm)?, ctx.fp_sqrt(else_, rm)?)?)
            } else {
                Ok(ctx.fp_sqrt(inner, rm)?)
            }
        }
        FloatOp::FpToFp(_, sort, rm) => {
            let sort = *sort;
            let rm = *rm;
            let inner = extract_float_child(children, 0)?;

            if let FloatOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_to_fp(then_, sort, rm)?,
                    ctx.fp_to_fp(else_, sort, rm)?,
                )?)
            } else {
                Ok(ctx.fp_to_fp(inner, sort, rm)?)
            }
        }
        FloatOp::BvToFp(_, sort) => {
            let sort = *sort;
            let inner = extract_bitvec_child(children, 0)?;

            if let BitVecOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.bv_to_fp(then_, sort)?, ctx.bv_to_fp(else_, sort)?)?)
            } else {
                Ok(ctx.bv_to_fp(inner, sort)?)
            }
        }
        FloatOp::BvToFpSigned(_, sort, rm) => {
            let sort = *sort;
            let rm = *rm;
            let inner = extract_bitvec_child(children, 0)?;

            if let BitVecOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.bv_to_fp_signed(then_, sort, rm)?,
                    ctx.bv_to_fp_signed(else_, sort, rm)?,
                )?)
            } else {
                Ok(ctx.bv_to_fp_signed(inner, sort, rm)?)
            }
        }
        FloatOp::BvToFpUnsigned(_, sort, rm) => {
            let sort = *sort;
            let rm = *rm;
            let inner = extract_bitvec_child(children, 0)?;

            if let BitVecOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.bv_to_fp_unsigned(then_, sort, rm)?,
                    ctx.bv_to_fp_unsigned(else_, sort, rm)?,
                )?)
            } else {
                Ok(ctx.bv_to_fp_unsigned(inner, sort, rm)?)
            }
        }
        FloatOp::FpFP(..) => {
            let sign = extract_bitvec_child(children, 0)?;
            let exponent = extract_bitvec_child(children, 1)?;
            let significand = extract_bitvec_child(children, 2)?;

            // Check sign for ITE
            if let BitVecOp::ITE(cond, then_, else_) = sign.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_fp(then_, &exponent, &significand)?,
                    ctx.fp_fp(else_, exponent, significand)?,
                )?)
            } else if let BitVecOp::ITE(cond, then_, else_) = exponent.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_fp(&sign, then_, &significand)?,
                    ctx.fp_fp(sign, else_, significand)?,
                )?)
            } else if let BitVecOp::ITE(cond, then_, else_) = significand.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_fp(&sign, &exponent, then_)?,
                    ctx.fp_fp(sign, exponent, else_)?,
                )?)
            } else {
                Ok(ctx.fp_fp(sign, exponent, significand)?)
            }
        }
        FloatOp::ITE(..) => {
            let cond = extract_bool_child(children, 0)?;
            let then_ = extract_float_child(children, 1)?;
            let else_ = extract_float_child(children, 2)?;

            Ok(ctx.ite(cond, then_, else_)?)
        }
    }
}
