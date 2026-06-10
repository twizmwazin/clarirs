use super::{
    extract_bitvec_child, extract_bool_child, extract_child, extract_float_child,
    extract_string_child,
};
use crate::prelude::*;

pub(crate) fn excavate_ite<'c>(
    ast: &AstRef<'c>,
    children: &[AstRef<'c>],
) -> Result<AstRef<'c>, ClarirsError> {
    let ctx = ast.context();

    match ast.op() {
        AstOp::BoolS(..) | AstOp::BoolV(..) => Ok(ast.clone()),
        AstOp::Not(..) => {
            let ast = extract_bool_child(children, 0)?;

            if let AstOp::ITE(cond, then_, else_) = ast.op() {
                Ok(ctx.ite(cond, ctx.not(then_)?, ctx.not(else_)?)?)
            } else {
                Ok(ctx.not(ast)?)
            }
        }
        AstOp::And(..) => {
            let args: Vec<_> = children
                .iter()
                .map(|c| extract_bool_child(std::slice::from_ref(c), 0))
                .collect::<Result<_, _>>()?;

            // Special case for binary And with two ITEs - expand all combinations
            if args.len() == 2
                && let (AstOp::ITE(cond1, then1, else1), AstOp::ITE(cond2, then2, else2)) =
                    (args[0].op(), args[1].op())
            {
                // Both are ITEs, expand to: ITE(cond1, ITE(cond2, then1&then2, then1&else2), ITE(cond2, else1&then2, else1&else2))
                return ctx.ite(
                    cond1,
                    ctx.ite(cond2, ctx.and2(then1, then2)?, ctx.and2(then1, else2)?)?,
                    ctx.ite(cond2, ctx.and2(else1, then2)?, ctx.and2(else1, else2)?)?,
                );
            }

            // Find first ITE among args
            if let Some((idx, (cond, then_, else_))) = args.iter().enumerate().find_map(|(i, a)| {
                if let AstOp::ITE(c, t, e) = a.op() {
                    Some((i, (c.clone(), t.clone(), e.clone())))
                } else {
                    None
                }
            }) {
                // Build And with then branch substituted
                let mut then_args: Vec<_> = args.clone();
                then_args[idx] = then_;
                let then_branch = ctx.and(then_args)?;

                // Build And with else branch substituted
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
                .map(|c| extract_bool_child(std::slice::from_ref(c), 0))
                .collect::<Result<_, _>>()?;

            // Special case for binary Or with two ITEs - expand all combinations
            if args.len() == 2
                && let (AstOp::ITE(cond1, then1, else1), AstOp::ITE(cond2, then2, else2)) =
                    (args[0].op(), args[1].op())
            {
                // Both are ITEs, expand to: ITE(cond1, ITE(cond2, then1|then2, then1|else2), ITE(cond2, else1|then2, else1|else2))
                return ctx.ite(
                    cond1,
                    ctx.ite(cond2, ctx.or2(then1, then2)?, ctx.or2(then1, else2)?)?,
                    ctx.ite(cond2, ctx.or2(else1, then2)?, ctx.or2(else1, else2)?)?,
                );
            }

            // Find first ITE among args
            if let Some((idx, (cond, then_, else_))) = args.iter().enumerate().find_map(|(i, a)| {
                if let AstOp::ITE(c, t, e) = a.op() {
                    Some((i, (c.clone(), t.clone(), e.clone())))
                } else {
                    None
                }
            }) {
                // Build Or with then branch substituted
                let mut then_args: Vec<_> = args.clone();
                then_args[idx] = then_;
                let then_branch = ctx.or(then_args)?;

                // Build Or with else branch substituted
                let mut else_args: Vec<_> = args;
                else_args[idx] = else_;
                let else_branch = ctx.or(else_args)?;

                Ok(ctx.ite(&cond, then_branch, else_branch)?)
            } else {
                ctx.or(args)
            }
        }
        AstOp::BoolXor(..) => {
            let lhs = extract_bool_child(children, 0)?;
            let rhs = extract_bool_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
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
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.xor(&lhs, then_)?, ctx.xor(lhs, else_)?)?)
            } else {
                Ok(ctx.xor(lhs, rhs)?)
            }
        }
        AstOp::Eq(..) => {
            let lhs = extract_child(children, 0)?;
            let rhs = extract_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
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
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.eq_(&lhs, then_)?, ctx.eq_(lhs, else_)?)?)
            } else {
                Ok(ctx.eq_(lhs, rhs)?)
            }
        }
        AstOp::Neq(..) => {
            let lhs = extract_child(children, 0)?;
            let rhs = extract_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
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
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.neq(&lhs, then_)?, ctx.neq(lhs, else_)?)?)
            } else {
                Ok(ctx.neq(lhs, rhs)?)
            }
        }
        AstOp::ULT(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.ult(then_, rhs_then)?,
                            ctx.ult(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.ult(else_, rhs_then)?,
                            ctx.ult(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.ult(then_, &rhs)?, ctx.ult(else_, rhs)?)?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.ult(&lhs, then_)?, ctx.ult(lhs, else_)?)?)
            } else {
                Ok(ctx.ult(lhs, rhs)?)
            }
        }
        AstOp::ULE(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.ule(then_, rhs_then)?,
                            ctx.ule(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.ule(else_, rhs_then)?,
                            ctx.ule(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.ule(then_, &rhs)?, ctx.ule(else_, rhs)?)?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.ule(&lhs, then_)?, ctx.ule(lhs, else_)?)?)
            } else {
                Ok(ctx.ule(lhs, rhs)?)
            }
        }
        AstOp::UGT(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.ugt(then_, rhs_then)?,
                            ctx.ugt(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.ugt(else_, rhs_then)?,
                            ctx.ugt(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.ugt(then_, &rhs)?, ctx.ugt(else_, rhs)?)?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.ugt(&lhs, then_)?, ctx.ugt(lhs, else_)?)?)
            } else {
                Ok(ctx.ugt(&lhs, rhs)?)
            }
        }
        AstOp::UGE(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.uge(then_, rhs_then)?,
                            ctx.uge(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.uge(else_, rhs_then)?,
                            ctx.uge(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.uge(then_, &rhs)?, ctx.uge(else_, rhs)?)?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.uge(&lhs, then_)?, ctx.uge(lhs, else_)?)?)
            } else {
                Ok(ctx.uge(lhs, rhs)?)
            }
        }
        AstOp::SLT(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.slt(then_, rhs_then)?,
                            ctx.slt(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.slt(else_, rhs_then)?,
                            ctx.slt(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.slt(then_, &rhs)?, ctx.slt(else_, rhs)?)?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.slt(&lhs, then_)?, ctx.slt(lhs, else_)?)?)
            } else {
                Ok(ctx.slt(lhs, rhs)?)
            }
        }
        AstOp::SLE(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.sle(then_, rhs_then)?,
                            ctx.sle(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.sle(else_, rhs_then)?,
                            ctx.sle(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.sle(then_, &rhs)?, ctx.sle(else_, rhs)?)?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.sle(&lhs, then_)?, ctx.sle(lhs, else_)?)?)
            } else {
                Ok(ctx.sle(lhs, rhs)?)
            }
        }
        AstOp::SGT(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.sgt(then_, rhs_then)?,
                            ctx.sgt(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.sgt(else_, rhs_then)?,
                            ctx.sgt(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.sgt(then_, &rhs)?, ctx.sgt(else_, rhs)?)?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.sgt(&lhs, then_)?, ctx.sgt(lhs, else_)?)?)
            } else {
                Ok(ctx.sgt(lhs, rhs)?)
            }
        }
        AstOp::SGE(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.sge(then_, rhs_then)?,
                            ctx.sge(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.sge(else_, rhs_then)?,
                            ctx.sge(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.sge(then_, &rhs)?, ctx.sge(else_, rhs)?)?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.sge(&lhs, then_)?, ctx.sge(lhs, else_)?)?)
            } else {
                Ok(ctx.sge(lhs, rhs)?)
            }
        }
        AstOp::FpLt(..) => {
            let lhs = extract_float_child(children, 0)?;
            let rhs = extract_float_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_lt(then_, rhs_then)?,
                            ctx.fp_lt(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_lt(else_, rhs_then)?,
                            ctx.fp_lt(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.fp_lt(then_, &rhs)?, ctx.fp_lt(else_, rhs)?)?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.fp_lt(&lhs, then_)?, ctx.fp_lt(lhs, else_)?)?)
            } else {
                Ok(ctx.fp_lt(lhs, rhs)?)
            }
        }
        AstOp::FpLeq(..) => {
            let lhs = extract_float_child(children, 0)?;
            let rhs = extract_float_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_leq(then_, rhs_then)?,
                            ctx.fp_leq(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_leq(else_, rhs_then)?,
                            ctx.fp_leq(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.fp_leq(then_, &rhs)?, ctx.fp_leq(else_, rhs)?)?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.fp_leq(&lhs, then_)?, ctx.fp_leq(lhs, else_)?)?)
            } else {
                Ok(ctx.fp_leq(lhs, rhs)?)
            }
        }
        AstOp::FpGt(..) => {
            let lhs = extract_float_child(children, 0)?;
            let rhs = extract_float_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_gt(then_, rhs_then)?,
                            ctx.fp_gt(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_gt(else_, rhs_then)?,
                            ctx.fp_gt(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.fp_gt(then_, &rhs)?, ctx.fp_gt(else_, rhs)?)?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.fp_gt(&lhs, then_)?, ctx.fp_gt(lhs, else_)?)?)
            } else {
                Ok(ctx.fp_gt(lhs, rhs)?)
            }
        }
        AstOp::FpGeq(..) => {
            let lhs = extract_float_child(children, 0)?;
            let rhs = extract_float_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_geq(then_, rhs_then)?,
                            ctx.fp_geq(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.fp_geq(else_, rhs_then)?,
                            ctx.fp_geq(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.fp_geq(then_, &rhs)?, ctx.fp_geq(else_, rhs)?)?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.fp_geq(&lhs, then_)?, ctx.fp_geq(lhs, else_)?)?)
            } else {
                Ok(ctx.fp_geq(lhs, rhs)?)
            }
        }
        AstOp::FpIsNan(..) => {
            let inner = extract_float_child(children, 0)?;

            if let AstOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.fp_is_nan(then_)?, ctx.fp_is_nan(else_)?)?)
            } else {
                Ok(ctx.fp_is_nan(inner)?)
            }
        }
        AstOp::FpIsInf(..) => {
            let inner = extract_float_child(children, 0)?;

            if let AstOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.fp_is_inf(then_)?, ctx.fp_is_inf(else_)?)?)
            } else {
                Ok(ctx.fp_is_inf(inner)?)
            }
        }
        AstOp::StrContains(..) => {
            let lhs = extract_string_child(children, 0)?;
            let rhs = extract_string_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.str_contains(then_, rhs_then)?,
                            ctx.str_contains(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.str_contains(else_, rhs_then)?,
                            ctx.str_contains(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(
                        cond,
                        ctx.str_contains(then_, &rhs)?,
                        ctx.str_contains(else_, rhs)?,
                    )?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_contains(&lhs, then_)?,
                    ctx.str_contains(lhs, else_)?,
                )?)
            } else {
                Ok(ctx.str_contains(lhs, rhs)?)
            }
        }
        AstOp::StrPrefixOf(..) => {
            let lhs = extract_string_child(children, 0)?;
            let rhs = extract_string_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.str_prefix_of(then_, rhs_then)?,
                            ctx.str_prefix_of(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.str_prefix_of(else_, rhs_then)?,
                            ctx.str_prefix_of(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(
                        cond,
                        ctx.str_prefix_of(then_, &rhs)?,
                        ctx.str_prefix_of(else_, rhs)?,
                    )?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_prefix_of(&lhs, then_)?,
                    ctx.str_prefix_of(lhs, else_)?,
                )?)
            } else {
                Ok(ctx.str_prefix_of(lhs, rhs)?)
            }
        }
        AstOp::StrSuffixOf(..) => {
            let lhs = extract_string_child(children, 0)?;
            let rhs = extract_string_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.str_suffix_of(then_, rhs_then)?,
                            ctx.str_suffix_of(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.str_suffix_of(else_, rhs_then)?,
                            ctx.str_suffix_of(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(
                        cond,
                        ctx.str_suffix_of(then_, &rhs)?,
                        ctx.str_suffix_of(else_, rhs)?,
                    )?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_suffix_of(&lhs, then_)?,
                    ctx.str_suffix_of(lhs, else_)?,
                )?)
            } else {
                Ok(ctx.str_suffix_of(lhs, rhs)?)
            }
        }
        AstOp::StrIsDigit(..) => {
            let inner = extract_string_child(children, 0)?;

            if let AstOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.str_is_digit(then_)?, ctx.str_is_digit(else_)?)?)
            } else {
                Ok(ctx.str_is_digit(inner)?)
            }
        }
        AstOp::ITE(..) => {
            let cond = extract_bool_child(children, 0)?;
            let then = extract_bool_child(children, 1)?;
            let else_ = extract_bool_child(children, 2)?;

            Ok(ctx.ite(cond, then, else_)?)
        }
        _ => unreachable!("non-boolean op dispatched to excavate_ite"),
    }
}
