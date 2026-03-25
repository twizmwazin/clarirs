use super::extract_child;
use crate::prelude::*;

pub(crate) fn excavate_ite<'c>(
    ast: &AstRef<'c>,
    children: &[AstRef<'c>],
) -> Result<AstRef<'c>, ClarirsError> {
    let ctx = ast.context();

    match ast.op() {
        Op::FPS(..) | Op::FPV(..) => Ok(ast.clone()),
        Op::FpNeg(..) => {
            let inner = extract_child(children, 0)?;

            if let Op::FpITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.fp_neg(then_)?, ctx.fp_neg(else_)?)?)
            } else {
                Ok(ctx.fp_neg(inner)?)
            }
        }
        Op::FpAbs(..) => {
            let inner = extract_child(children, 0)?;

            if let Op::FpITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.fp_abs(then_)?, ctx.fp_abs(else_)?)?)
            } else {
                Ok(ctx.fp_abs(inner)?)
            }
        }
        Op::FpAdd(_, _, rm) => {
            let rm = *rm;
            let lhs = extract_child(children, 0)?;
            let rhs = extract_child(children, 1)?;

            if let Op::FpITE(cond, then_, else_) = lhs.op() {
                if let Op::FpITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
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
            } else if let Op::FpITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_add(&lhs, then_, rm)?,
                    ctx.fp_add(lhs, else_, rm)?,
                )?)
            } else {
                Ok(ctx.fp_add(lhs, rhs, rm)?)
            }
        }
        Op::FpSub(_, _, rm) => {
            let rm = *rm;
            let lhs = extract_child(children, 0)?;
            let rhs = extract_child(children, 1)?;

            if let Op::FpITE(cond, then_, else_) = lhs.op() {
                if let Op::FpITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
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
            } else if let Op::FpITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_sub(&lhs, then_, rm)?,
                    ctx.fp_sub(lhs, else_, rm)?,
                )?)
            } else {
                Ok(ctx.fp_sub(lhs, rhs, rm)?)
            }
        }
        Op::FpMul(_, _, rm) => {
            let rm = *rm;
            let lhs = extract_child(children, 0)?;
            let rhs = extract_child(children, 1)?;

            if let Op::FpITE(cond, then_, else_) = lhs.op() {
                if let Op::FpITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
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
            } else if let Op::FpITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_mul(&lhs, then_, rm)?,
                    ctx.fp_mul(lhs, else_, rm)?,
                )?)
            } else {
                Ok(ctx.fp_mul(lhs, rhs, rm)?)
            }
        }
        Op::FpDiv(_, _, rm) => {
            let rm = *rm;
            let lhs = extract_child(children, 0)?;
            let rhs = extract_child(children, 1)?;

            if let Op::FpITE(cond, then_, else_) = lhs.op() {
                if let Op::FpITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
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
            } else if let Op::FpITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_div(&lhs, then_, rm)?,
                    ctx.fp_div(lhs, else_, rm)?,
                )?)
            } else {
                Ok(ctx.fp_div(lhs, rhs, rm)?)
            }
        }
        Op::FpSqrt(_, rm) => {
            let rm = *rm;
            let inner = extract_child(children, 0)?;

            if let Op::FpITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.fp_sqrt(then_, rm)?, ctx.fp_sqrt(else_, rm)?)?)
            } else {
                Ok(ctx.fp_sqrt(inner, rm)?)
            }
        }
        Op::FpToFp(_, sort, rm) => {
            let sort = *sort;
            let rm = *rm;
            let inner = extract_child(children, 0)?;

            if let Op::FpITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_to_fp(then_, sort, rm)?,
                    ctx.fp_to_fp(else_, sort, rm)?,
                )?)
            } else {
                Ok(ctx.fp_to_fp(inner, sort, rm)?)
            }
        }
        Op::BvToFp(_, sort) => {
            let sort = *sort;
            let inner = extract_child(children, 0)?;

            if let Op::BVITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.bv_to_fp(then_, sort)?, ctx.bv_to_fp(else_, sort)?)?)
            } else {
                Ok(ctx.bv_to_fp(inner, sort)?)
            }
        }
        Op::BvToFpSigned(_, sort, rm) => {
            let sort = *sort;
            let rm = *rm;
            let inner = extract_child(children, 0)?;

            if let Op::BVITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.bv_to_fp_signed(then_, sort, rm)?,
                    ctx.bv_to_fp_signed(else_, sort, rm)?,
                )?)
            } else {
                Ok(ctx.bv_to_fp_signed(inner, sort, rm)?)
            }
        }
        Op::BvToFpUnsigned(_, sort, rm) => {
            let sort = *sort;
            let rm = *rm;
            let inner = extract_child(children, 0)?;

            if let Op::BVITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.bv_to_fp_unsigned(then_, sort, rm)?,
                    ctx.bv_to_fp_unsigned(else_, sort, rm)?,
                )?)
            } else {
                Ok(ctx.bv_to_fp_unsigned(inner, sort, rm)?)
            }
        }
        Op::FpFP(..) => {
            let sign = extract_child(children, 0)?;
            let exponent = extract_child(children, 1)?;
            let significand = extract_child(children, 2)?;

            // Check sign for ITE
            if let Op::BVITE(cond, then_, else_) = sign.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_fp(then_, &exponent, &significand)?,
                    ctx.fp_fp(else_, exponent, significand)?,
                )?)
            } else if let Op::BVITE(cond, then_, else_) = exponent.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_fp(&sign, then_, &significand)?,
                    ctx.fp_fp(sign, else_, significand)?,
                )?)
            } else if let Op::BVITE(cond, then_, else_) = significand.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_fp(&sign, &exponent, then_)?,
                    ctx.fp_fp(sign, exponent, else_)?,
                )?)
            } else {
                Ok(ctx.fp_fp(sign, exponent, significand)?)
            }
        }
        Op::FpITE(..) => {
            let cond = extract_child(children, 0)?;
            let then_ = extract_child(children, 1)?;
            let else_ = extract_child(children, 2)?;

            Ok(ctx.ite(cond, then_, else_)?)
        }
        _ => Ok(ast.clone()),
    }
}
