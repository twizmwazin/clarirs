use super::extract_child;
use crate::prelude::*;

pub(crate) fn excavate_ite<'c>(
    ast: &AstRef<'c>,
    children: &[AstRef<'c>],
) -> Result<AstRef<'c>, ClarirsError> {
    let ctx = ast.context();

    match ast.op() {
        AstOp::BoolS(..) | AstOp::BoolV(..) => Ok(ast.clone()),
        AstOp::Not(..) => {
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.not(then_)?, ctx.not(else_)?)?)
            } else {
                Ok(ctx.not(inner)?)
            }
        }
        AstOp::And(..) => {
            let args: Vec<_> = children
                .iter()
                .map(|c| extract_child(std::slice::from_ref(c), 0))
                .collect::<Result<_, _>>()?;

            // Special case for binary And with two ITEs - expand all combinations
            if args.len() == 2
                && let (AstOp::If(cond1, then1, else1), AstOp::If(cond2, then2, else2)) =
                    (args[0].op(), args[1].op())
            {
                return ctx.ite(
                    cond1,
                    ctx.ite(cond2, ctx.and2(then1, then2)?, ctx.and2(then1, else2)?)?,
                    ctx.ite(cond2, ctx.and2(else1, then2)?, ctx.and2(else1, else2)?)?,
                );
            }

            // Find first ITE among args
            if let Some((idx, (cond, then_, else_))) = args.iter().enumerate().find_map(|(i, a)| {
                if let AstOp::If(c, t, e) = a.op() {
                    Some((i, (c.clone(), t.clone(), e.clone())))
                } else {
                    None
                }
            }) {
                let mut then_args: Vec<_> = args.clone();
                then_args[idx] = then_;
                let then_branch = ctx.and(then_args)?;

                let mut else_args: Vec<_> = args;
                else_args[idx] = else_;
                let else_branch = ctx.and(else_args)?;

                Ok(ctx.ite(&cond, then_branch, else_branch)?)
            } else {
                ctx.and(args)
            }
        }
        AstOp::Or(..) => {
            let args: Vec<_> = children
                .iter()
                .map(|c| extract_child(std::slice::from_ref(c), 0))
                .collect::<Result<_, _>>()?;

            // Special case for binary Or with two ITEs - expand all combinations
            if args.len() == 2
                && let (AstOp::If(cond1, then1, else1), AstOp::If(cond2, then2, else2)) =
                    (args[0].op(), args[1].op())
            {
                return ctx.ite(
                    cond1,
                    ctx.ite(cond2, ctx.or2(then1, then2)?, ctx.or2(then1, else2)?)?,
                    ctx.ite(cond2, ctx.or2(else1, then2)?, ctx.or2(else1, else2)?)?,
                );
            }

            // Find first ITE among args
            if let Some((idx, (cond, then_, else_))) = args.iter().enumerate().find_map(|(i, a)| {
                if let AstOp::If(c, t, e) = a.op() {
                    Some((i, (c.clone(), t.clone(), e.clone())))
                } else {
                    None
                }
            }) {
                let mut then_args: Vec<_> = args.clone();
                then_args[idx] = then_;
                let then_branch = ctx.or(then_args)?;

                let mut else_args: Vec<_> = args;
                else_args[idx] = else_;
                let else_branch = ctx.or(else_args)?;

                Ok(ctx.ite(&cond, then_branch, else_branch)?)
            } else {
                ctx.or(args)
            }
        }
        AstOp::Xor(..) => {
            let lhs = extract_child(children, 0)?;
            let rhs = extract_child(children, 1)?;

            if let AstOp::If(cond, then_, else_) = lhs.op() {
                if let AstOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.xor(then_, rhs_then)?,
                            ctx.xor(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.xor(else_, rhs_then)?,
                            ctx.xor(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.xor(then_, &rhs)?, ctx.xor(else_, rhs)?)?)
                }
            } else if let AstOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.xor(&lhs, then_)?, ctx.xor(lhs, else_)?)?)
            } else {
                Ok(ctx.xor(lhs, rhs)?)
            }
        }
        AstOp::Eq(..) => {
            let lhs = extract_child(children, 0)?;
            let rhs = extract_child(children, 1)?;

            if let AstOp::If(cond, then_, else_) = lhs.op() {
                if let AstOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.eq_(then_, rhs_then)?,
                            ctx.eq_(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.eq_(else_, rhs_then)?,
                            ctx.eq_(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.eq_(then_, &rhs)?, ctx.eq_(else_, rhs)?)?)
                }
            } else if let AstOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.eq_(&lhs, then_)?, ctx.eq_(lhs, else_)?)?)
            } else {
                Ok(ctx.eq_(lhs, rhs)?)
            }
        }
        AstOp::Neq(..) => {
            let lhs = extract_child(children, 0)?;
            let rhs = extract_child(children, 1)?;

            if let AstOp::If(cond, then_, else_) = lhs.op() {
                if let AstOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.neq(then_, rhs_then)?,
                            ctx.neq(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.neq(else_, rhs_then)?,
                            ctx.neq(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.neq(then_, &rhs)?, ctx.neq(else_, rhs)?)?)
                }
            } else if let AstOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.neq(&lhs, then_)?, ctx.neq(lhs, else_)?)?)
            } else {
                Ok(ctx.neq(lhs, rhs)?)
            }
        }
        AstOp::ULT(..) => excavate_binary_cmp(ctx, children, |ctx, a, b| ctx.ult(a, b)),
        AstOp::ULE(..) => excavate_binary_cmp(ctx, children, |ctx, a, b| ctx.ule(a, b)),
        AstOp::UGT(..) => excavate_binary_cmp(ctx, children, |ctx, a, b| ctx.ugt(a, b)),
        AstOp::UGE(..) => excavate_binary_cmp(ctx, children, |ctx, a, b| ctx.uge(a, b)),
        AstOp::SLT(..) => excavate_binary_cmp(ctx, children, |ctx, a, b| ctx.slt(a, b)),
        AstOp::SLE(..) => excavate_binary_cmp(ctx, children, |ctx, a, b| ctx.sle(a, b)),
        AstOp::SGT(..) => excavate_binary_cmp(ctx, children, |ctx, a, b| ctx.sgt(a, b)),
        AstOp::SGE(..) => excavate_binary_cmp(ctx, children, |ctx, a, b| ctx.sge(a, b)),
        AstOp::FpLt(..) => excavate_binary_cmp(ctx, children, |ctx, a, b| ctx.fp_lt(a, b)),
        AstOp::FpLeq(..) => excavate_binary_cmp(ctx, children, |ctx, a, b| ctx.fp_leq(a, b)),
        AstOp::FpGt(..) => excavate_binary_cmp(ctx, children, |ctx, a, b| ctx.fp_gt(a, b)),
        AstOp::FpGeq(..) => excavate_binary_cmp(ctx, children, |ctx, a, b| ctx.fp_geq(a, b)),
        AstOp::StrContains(..) => {
            excavate_binary_cmp(ctx, children, |ctx, a, b| ctx.str_contains(a, b))
        }
        AstOp::StrPrefixOf(..) => {
            excavate_binary_cmp(ctx, children, |ctx, a, b| ctx.str_prefix_of(a, b))
        }
        AstOp::StrSuffixOf(..) => {
            excavate_binary_cmp(ctx, children, |ctx, a, b| ctx.str_suffix_of(a, b))
        }
        AstOp::FpIsNan(..) => {
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.fp_is_nan(then_)?, ctx.fp_is_nan(else_)?)?)
            } else {
                Ok(ctx.fp_is_nan(inner)?)
            }
        }
        AstOp::FpIsInf(..) => {
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.fp_is_inf(then_)?, ctx.fp_is_inf(else_)?)?)
            } else {
                Ok(ctx.fp_is_inf(inner)?)
            }
        }
        AstOp::StrIsDigit(..) => {
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.str_is_digit(then_)?, ctx.str_is_digit(else_)?)?)
            } else {
                Ok(ctx.str_is_digit(inner)?)
            }
        }
        AstOp::If(..) => {
            let cond = extract_child(children, 0)?;
            let then_ = extract_child(children, 1)?;
            let else_ = extract_child(children, 2)?;

            Ok(ctx.ite(cond, then_, else_)?)
        }
        _ => unreachable!("bool::excavate_ite called with non-bool op: {:?}", ast.op()),
    }
}

/// Helper for binary comparison operations that produce a boolean result.
/// Handles excavation of If nodes in both operands.
fn excavate_binary_cmp<'c>(
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
