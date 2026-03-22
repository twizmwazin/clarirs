use super::extract_child;
use crate::prelude::*;

pub(crate) fn excavate_ite<'c>(
    ast: &AstRef<'c>,
    children: &[AstRef<'c>],
) -> Result<AstRef<'c>, ClarirsError> {
    let ctx = ast.context();

    match ast.op() {
        AstOp::FPS(..) | AstOp::FPV(..) => Ok(ast.clone()),
        AstOp::FpNeg(..) => {
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.fp_neg(then_)?, ctx.fp_neg(else_)?)?)
            } else {
                Ok(ctx.fp_neg(inner)?)
            }
        }
        AstOp::FpAbs(..) => {
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.fp_abs(then_)?, ctx.fp_abs(else_)?)?)
            } else {
                Ok(ctx.fp_abs(inner)?)
            }
        }
        AstOp::FpAdd(_, _, rm) => {
            let rm = *rm;
            excavate_binary_fp(ctx, children, move |ctx, a, b| ctx.fp_add(a, b, rm))
        }
        AstOp::FpSub(_, _, rm) => {
            let rm = *rm;
            excavate_binary_fp(ctx, children, move |ctx, a, b| ctx.fp_sub(a, b, rm))
        }
        AstOp::FpMul(_, _, rm) => {
            let rm = *rm;
            excavate_binary_fp(ctx, children, move |ctx, a, b| ctx.fp_mul(a, b, rm))
        }
        AstOp::FpDiv(_, _, rm) => {
            let rm = *rm;
            excavate_binary_fp(ctx, children, move |ctx, a, b| ctx.fp_div(a, b, rm))
        }
        AstOp::FpSqrt(_, rm) => {
            let rm = *rm;
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.fp_sqrt(then_, rm)?, ctx.fp_sqrt(else_, rm)?)?)
            } else {
                Ok(ctx.fp_sqrt(inner, rm)?)
            }
        }
        AstOp::FpToFp(_, sort, rm) => {
            let sort = *sort;
            let rm = *rm;
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_to_fp(then_, sort, rm)?,
                    ctx.fp_to_fp(else_, sort, rm)?,
                )?)
            } else {
                Ok(ctx.fp_to_fp(inner, sort, rm)?)
            }
        }
        AstOp::BvToFp(_, sort) => {
            let sort = *sort;
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.bv_to_fp(then_, sort)?, ctx.bv_to_fp(else_, sort)?)?)
            } else {
                Ok(ctx.bv_to_fp(inner, sort)?)
            }
        }
        AstOp::BvToFpSigned(_, sort, rm) => {
            let sort = *sort;
            let rm = *rm;
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.bv_to_fp_signed(then_, sort, rm)?,
                    ctx.bv_to_fp_signed(else_, sort, rm)?,
                )?)
            } else {
                Ok(ctx.bv_to_fp_signed(inner, sort, rm)?)
            }
        }
        AstOp::BvToFpUnsigned(_, sort, rm) => {
            let sort = *sort;
            let rm = *rm;
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.bv_to_fp_unsigned(then_, sort, rm)?,
                    ctx.bv_to_fp_unsigned(else_, sort, rm)?,
                )?)
            } else {
                Ok(ctx.bv_to_fp_unsigned(inner, sort, rm)?)
            }
        }
        AstOp::FpFP(..) => {
            let sign = extract_child(children, 0)?;
            let exponent = extract_child(children, 1)?;
            let significand = extract_child(children, 2)?;

            // Check sign for ITE
            if let AstOp::If(cond, then_, else_) = sign.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_fp(then_, &exponent, &significand)?,
                    ctx.fp_fp(else_, exponent, significand)?,
                )?)
            } else if let AstOp::If(cond, then_, else_) = exponent.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_fp(&sign, then_, &significand)?,
                    ctx.fp_fp(sign, else_, significand)?,
                )?)
            } else if let AstOp::If(cond, then_, else_) = significand.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_fp(&sign, &exponent, then_)?,
                    ctx.fp_fp(sign, exponent, else_)?,
                )?)
            } else {
                Ok(ctx.fp_fp(sign, exponent, significand)?)
            }
        }
        AstOp::If(..) => {
            let cond = extract_child(children, 0)?;
            let then_ = extract_child(children, 1)?;
            let else_ = extract_child(children, 2)?;

            Ok(ctx.ite(cond, then_, else_)?)
        }
        _ => unreachable!(
            "float::excavate_ite called with non-float op: {:?}",
            ast.op()
        ),
    }
}

/// Helper for binary float operations with full ITE expansion.
fn excavate_binary_fp<'c>(
    ctx: &'c Context<'c>,
    children: &[AstRef<'c>],
    op_fn: impl Fn(&'c Context<'c>, &AstRef<'c>, &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError>,
) -> Result<AstRef<'c>, ClarirsError> {
    let lhs = extract_child(children, 0)?;
    let rhs = extract_child(children, 1)?;

    if let AstOp::If(cond, then_, else_) = lhs.op() {
        if let AstOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
            Ok(ctx.ite(
                cond,
                ctx.ite(
                    rhs_cond,
                    op_fn(ctx, then_, rhs_then)?,
                    op_fn(ctx, then_, rhs_else)?,
                )?,
                ctx.ite(
                    rhs_cond,
                    op_fn(ctx, else_, rhs_then)?,
                    op_fn(ctx, else_, rhs_else)?,
                )?,
            )?)
        } else {
            Ok(ctx.ite(cond, op_fn(ctx, then_, &rhs)?, op_fn(ctx, else_, &rhs)?)?)
        }
    } else if let AstOp::If(cond, then_, else_) = rhs.op() {
        Ok(ctx.ite(cond, op_fn(ctx, &lhs, then_)?, op_fn(ctx, &lhs, else_)?)?)
    } else {
        op_fn(ctx, &lhs, &rhs)
    }
}
