use super::extract_child;
use crate::prelude::*;

pub(crate) fn excavate_ite<'c>(
    ast: &AstRef<'c>,
    children: &[AstRef<'c>],
) -> Result<AstRef<'c>, ClarirsError> {
    let ctx = ast.context();

    match ast.op() {
        AstOp::BVS(..) | AstOp::BVV(..) => Ok(ast.clone()),
        AstOp::Not(..) => {
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.not(then_)?, ctx.not(else_)?)?)
            } else {
                Ok(ctx.not(inner)?)
            }
        }
        AstOp::And(args) => {
            let excavated_args: Vec<AstRef<'c>> = (0..args.len())
                .map(|i| extract_child(children, i))
                .collect::<Result<_, _>>()?;

            let ite_idx = excavated_args
                .iter()
                .position(|arg| matches!(arg.op(), AstOp::If(..)));

            if let Some(idx) = ite_idx {
                let (cond, then_, else_) = if let AstOp::If(c, t, e) = excavated_args[idx].op() {
                    (c.clone(), t.clone(), e.clone())
                } else {
                    unreachable!()
                };

                let mut then_args = excavated_args.clone();
                then_args[idx] = then_;
                let mut else_args = excavated_args;
                else_args[idx] = else_;

                Ok(ctx.ite(
                    &cond,
                    ctx.bv_and_many(then_args)?,
                    ctx.bv_and_many(else_args)?,
                )?)
            } else {
                ctx.bv_and_many(excavated_args)
            }
        }
        AstOp::Or(args) => {
            let excavated_args: Vec<AstRef<'c>> = (0..args.len())
                .map(|i| extract_child(children, i))
                .collect::<Result<_, _>>()?;

            let ite_idx = excavated_args
                .iter()
                .position(|arg| matches!(arg.op(), AstOp::If(..)));

            if let Some(idx) = ite_idx {
                let (cond, then_, else_) = if let AstOp::If(c, t, e) = excavated_args[idx].op() {
                    (c.clone(), t.clone(), e.clone())
                } else {
                    unreachable!()
                };

                let mut then_args = excavated_args.clone();
                then_args[idx] = then_;
                let mut else_args = excavated_args;
                else_args[idx] = else_;

                Ok(ctx.ite(
                    &cond,
                    ctx.bv_or_many(then_args)?,
                    ctx.bv_or_many(else_args)?,
                )?)
            } else {
                ctx.bv_or_many(excavated_args)
            }
        }
        AstOp::Xor(args) => {
            let excavated_args: Vec<AstRef<'c>> = (0..args.len())
                .map(|i| extract_child(children, i))
                .collect::<Result<_, _>>()?;

            let ite_idx = excavated_args
                .iter()
                .position(|arg| matches!(arg.op(), AstOp::If(..)));

            if let Some(idx) = ite_idx {
                let (cond, then_, else_) = if let AstOp::If(c, t, e) = excavated_args[idx].op() {
                    (c.clone(), t.clone(), e.clone())
                } else {
                    unreachable!()
                };

                let mut then_args = excavated_args.clone();
                then_args[idx] = then_;
                let mut else_args = excavated_args;
                else_args[idx] = else_;

                Ok(ctx.ite(
                    &cond,
                    ctx.bv_xor_many(then_args)?,
                    ctx.bv_xor_many(else_args)?,
                )?)
            } else {
                ctx.bv_xor_many(excavated_args)
            }
        }
        AstOp::Neg(..) => {
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.neg(then_)?, ctx.neg(else_)?)?)
            } else {
                Ok(ctx.neg(inner)?)
            }
        }
        AstOp::Add(args) => {
            let excavated_args: Vec<AstRef<'c>> = (0..args.len())
                .map(|i| extract_child(children, i))
                .collect::<Result<_, _>>()?;

            let ite_idx = excavated_args
                .iter()
                .position(|arg| matches!(arg.op(), AstOp::If(..)));

            if let Some(idx) = ite_idx {
                let (cond, then_, else_) = if let AstOp::If(c, t, e) = excavated_args[idx].op() {
                    (c.clone(), t.clone(), e.clone())
                } else {
                    unreachable!()
                };

                let mut then_args = excavated_args.clone();
                then_args[idx] = then_;
                let mut else_args = excavated_args;
                else_args[idx] = else_;

                Ok(ctx.ite(&cond, ctx.add_many(then_args)?, ctx.add_many(else_args)?)?)
            } else {
                ctx.add_many(excavated_args)
            }
        }
        AstOp::Sub(..) => excavate_binary_bv(ctx, children, |ctx, a, b| ctx.sub(a, b)),
        AstOp::Mul(args) => {
            let excavated_args: Vec<AstRef<'c>> = (0..args.len())
                .map(|i| extract_child(children, i))
                .collect::<Result<_, _>>()?;

            let ite_idx = excavated_args
                .iter()
                .position(|arg| matches!(arg.op(), AstOp::If(..)));

            if let Some(idx) = ite_idx {
                let (cond, then_, else_) = if let AstOp::If(c, t, e) = excavated_args[idx].op() {
                    (c.clone(), t.clone(), e.clone())
                } else {
                    unreachable!()
                };

                let mut then_args = excavated_args.clone();
                then_args[idx] = then_;
                let mut else_args = excavated_args;
                else_args[idx] = else_;

                Ok(ctx.ite(&cond, ctx.mul_many(then_args)?, ctx.mul_many(else_args)?)?)
            } else {
                ctx.mul_many(excavated_args)
            }
        }
        AstOp::UDiv(..) => excavate_binary_bv(ctx, children, |ctx, a, b| ctx.udiv(a, b)),
        AstOp::SDiv(..) => excavate_binary_bv(ctx, children, |ctx, a, b| ctx.sdiv(a, b)),
        AstOp::URem(..) => excavate_binary_bv(ctx, children, |ctx, a, b| ctx.urem(a, b)),
        AstOp::SRem(..) => excavate_binary_bv(ctx, children, |ctx, a, b| ctx.srem(a, b)),
        AstOp::ShL(..) => excavate_binary_bv(ctx, children, |ctx, a, b| ctx.shl(a, b)),
        AstOp::LShR(..) => excavate_binary_bv(ctx, children, |ctx, a, b| ctx.lshr(a, b)),
        AstOp::AShR(..) => excavate_binary_bv(ctx, children, |ctx, a, b| ctx.ashr(a, b)),
        AstOp::RotateLeft(..) => {
            excavate_binary_bv(ctx, children, |ctx, a, b| ctx.rotate_left(a, b))
        }
        AstOp::RotateRight(..) => {
            excavate_binary_bv(ctx, children, |ctx, a, b| ctx.rotate_right(a, b))
        }
        AstOp::ZeroExt(_, amount) => {
            let amount = *amount;
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.zero_ext(then_, amount)?,
                    ctx.zero_ext(else_, amount)?,
                )?)
            } else {
                Ok(ctx.zero_ext(inner, amount)?)
            }
        }
        AstOp::SignExt(_, amount) => {
            let amount = *amount;
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.sign_ext(then_, amount)?,
                    ctx.sign_ext(else_, amount)?,
                )?)
            } else {
                Ok(ctx.sign_ext(inner, amount)?)
            }
        }
        AstOp::Extract(_, ub, lb) => {
            let ub = *ub;
            let lb = *lb;
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.extract(then_, ub, lb)?,
                    ctx.extract(else_, ub, lb)?,
                )?)
            } else {
                Ok(ctx.extract(inner, ub, lb)?)
            }
        }
        AstOp::Concat(args) => {
            let excavated_args: Vec<AstRef<'c>> = (0..args.len())
                .map(|i| extract_child(children, i))
                .collect::<Result<_, _>>()?;

            let ite_idx = excavated_args
                .iter()
                .position(|arg| matches!(arg.op(), AstOp::If(..)));

            if let Some(idx) = ite_idx {
                let (cond, then_, else_) = if let AstOp::If(c, t, e) = excavated_args[idx].op() {
                    (c.clone(), t.clone(), e.clone())
                } else {
                    unreachable!()
                };

                let mut then_args = excavated_args.clone();
                then_args[idx] = then_;
                let mut else_args = excavated_args;
                else_args[idx] = else_;

                Ok(ctx.ite(&cond, ctx.concat(then_args)?, ctx.concat(else_args)?)?)
            } else {
                ctx.concat(excavated_args)
            }
        }
        AstOp::ByteReverse(..) => {
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.byte_reverse(then_)?, ctx.byte_reverse(else_)?)?)
            } else {
                Ok(ctx.byte_reverse(inner)?)
            }
        }
        AstOp::FpToIEEEBV(..) => {
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.fp_to_ieeebv(then_)?, ctx.fp_to_ieeebv(else_)?)?)
            } else {
                Ok(ctx.fp_to_ieeebv(inner)?)
            }
        }
        AstOp::FpToUBV(_, width, rm) => {
            let width = *width;
            let rm = *rm;
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_to_ubv(then_, width, rm)?,
                    ctx.fp_to_ubv(else_, width, rm)?,
                )?)
            } else {
                Ok(ctx.fp_to_ubv(inner, width, rm)?)
            }
        }
        AstOp::FpToSBV(_, width, rm) => {
            let width = *width;
            let rm = *rm;
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_to_sbv(then_, width, rm)?,
                    ctx.fp_to_sbv(else_, width, rm)?,
                )?)
            } else {
                Ok(ctx.fp_to_sbv(inner, width, rm)?)
            }
        }
        AstOp::StrLen(..) => {
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.str_len(then_)?, ctx.str_len(else_)?)?)
            } else {
                Ok(ctx.str_len(inner)?)
            }
        }
        AstOp::StrIndexOf(..) => {
            let base = extract_child(children, 0)?;
            let substr = extract_child(children, 1)?;
            let offset = extract_child(children, 2)?;

            if let AstOp::If(cond, then_, else_) = base.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_index_of(then_, &substr, &offset)?,
                    ctx.str_index_of(else_, substr, offset)?,
                )?)
            } else if let AstOp::If(cond, then_, else_) = substr.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_index_of(&base, then_, &offset)?,
                    ctx.str_index_of(base, else_, offset)?,
                )?)
            } else if let AstOp::If(cond, then_, else_) = offset.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_index_of(&base, &substr, then_)?,
                    ctx.str_index_of(base, substr, else_)?,
                )?)
            } else {
                Ok(ctx.str_index_of(base, substr, offset)?)
            }
        }
        AstOp::StrToBV(..) => {
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.str_to_bv(then_)?, ctx.str_to_bv(else_)?)?)
            } else {
                Ok(ctx.str_to_bv(inner)?)
            }
        }
        AstOp::If(..) => {
            let cond = extract_child(children, 0)?;
            let then_ = extract_child(children, 1)?;
            let else_ = extract_child(children, 2)?;

            Ok(ctx.ite(cond, then_, else_)?)
        }
        AstOp::Union(..) => excavate_binary_bv(ctx, children, |ctx, a, b| ctx.union(a, b)),
        AstOp::Intersection(..) => {
            excavate_binary_bv(ctx, children, |ctx, a, b| ctx.intersection(a, b))
        }
        AstOp::Widen(..) => excavate_binary_bv(ctx, children, |ctx, a, b| ctx.widen(a, b)),
        _ => unreachable!(
            "bitvec::excavate_ite called with non-bitvec op: {:?}",
            ast.op()
        ),
    }
}

/// Helper for binary bitvec operations.
/// Handles excavation of If nodes in both operands, prioritizing left condition.
fn excavate_binary_bv<'c>(
    ctx: &'c Context<'c>,
    children: &[AstRef<'c>],
    op_fn: impl Fn(
        &'c Context<'c>,
        &AstRef<'c>,
        &AstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError>,
) -> Result<AstRef<'c>, ClarirsError> {
    let lhs = extract_child(children, 0)?;
    let rhs = extract_child(children, 1)?;

    if let AstOp::If(cond, then_, else_) = lhs.op() {
        if let AstOp::If(_, rhs_then, rhs_else) = rhs.op() {
            // Prioritize left condition as outer if
            Ok(ctx.ite(
                cond,
                op_fn(ctx, then_, rhs_then)?,
                op_fn(ctx, then_, rhs_else)?,
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
