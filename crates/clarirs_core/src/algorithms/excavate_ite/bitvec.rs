use super::{extract_bitvec_child, extract_bool_child, extract_float_child, extract_string_child};
use crate::prelude::*;

pub(crate) fn excavate_ite<'c>(
    ast: &BitVecAst<'c>,
    children: &[DynAst<'c>],
) -> Result<BitVecAst<'c>, ClarirsError> {
    let ctx = ast.context();

    match ast.op() {
        BitVecOp::BVS(..) | BitVecOp::BVV(..) => Ok(ast.clone()),
        BitVecOp::Not(..) => {
            let ast = extract_bitvec_child(children, 0)?;

            if let BitVecOp::ITE(cond, then_, else_) = ast.op() {
                Ok(ctx.ite(cond, ctx.not(then_)?, ctx.not(else_)?)?)
            } else {
                Ok(ctx.not(ast)?)
            }
        }
        BitVecOp::And(args) => {
            let excavated_args: Vec<BitVecAst<'c>> = (0..args.len())
                .map(|i| extract_bitvec_child(children, i))
                .collect::<Result<_, _>>()?;

            let ite_idx = excavated_args
                .iter()
                .position(|arg| matches!(arg.op(), BitVecOp::ITE(..)));

            if let Some(idx) = ite_idx {
                let (cond, then_, else_) = if let BitVecOp::ITE(c, t, e) = excavated_args[idx].op()
                {
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
        BitVecOp::Or(args) => {
            let excavated_args: Vec<BitVecAst<'c>> = (0..args.len())
                .map(|i| extract_bitvec_child(children, i))
                .collect::<Result<_, _>>()?;

            let ite_idx = excavated_args
                .iter()
                .position(|arg| matches!(arg.op(), BitVecOp::ITE(..)));

            if let Some(idx) = ite_idx {
                let (cond, then_, else_) = if let BitVecOp::ITE(c, t, e) = excavated_args[idx].op()
                {
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
        BitVecOp::Xor(args) => {
            let excavated_args: Vec<BitVecAst<'c>> = (0..args.len())
                .map(|i| extract_bitvec_child(children, i))
                .collect::<Result<_, _>>()?;

            let ite_idx = excavated_args
                .iter()
                .position(|arg| matches!(arg.op(), BitVecOp::ITE(..)));

            if let Some(idx) = ite_idx {
                let (cond, then_, else_) = if let BitVecOp::ITE(c, t, e) = excavated_args[idx].op()
                {
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
        BitVecOp::Neg(..) => {
            let ast = extract_bitvec_child(children, 0)?;

            if let BitVecOp::ITE(cond, then_, else_) = ast.op() {
                Ok(ctx.ite(cond, ctx.neg(then_)?, ctx.neg(else_)?)?)
            } else {
                Ok(ctx.neg(ast)?)
            }
        }
        BitVecOp::Add(args) => {
            let excavated_args: Vec<BitVecAst<'c>> = (0..args.len())
                .map(|i| extract_bitvec_child(children, i))
                .collect::<Result<_, _>>()?;

            let ite_idx = excavated_args
                .iter()
                .position(|arg| matches!(arg.op(), BitVecOp::ITE(..)));

            if let Some(idx) = ite_idx {
                let (cond, then_, else_) = if let BitVecOp::ITE(c, t, e) = excavated_args[idx].op()
                {
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
        BitVecOp::Sub(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(cond, ctx.sub(then_, rhs_then)?, ctx.sub(then_, rhs_else)?)?)
                } else {
                    Ok(ctx.ite(cond, ctx.sub(then_, &rhs)?, ctx.sub(else_, rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.sub(&lhs, then_)?, ctx.sub(lhs, else_)?)?)
            } else {
                Ok(ctx.sub(lhs, rhs)?)
            }
        }
        BitVecOp::Mul(args) => {
            let excavated_args: Vec<BitVecAst<'c>> = (0..args.len())
                .map(|i| extract_bitvec_child(children, i))
                .collect::<Result<_, _>>()?;

            let ite_idx = excavated_args
                .iter()
                .position(|arg| matches!(arg.op(), BitVecOp::ITE(..)));

            if let Some(idx) = ite_idx {
                let (cond, then_, else_) = if let BitVecOp::ITE(c, t, e) = excavated_args[idx].op()
                {
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
        BitVecOp::UDiv(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(cond, ctx.udiv(then_, rhs_then)?, ctx.udiv(then_, rhs_else)?)?)
                } else {
                    Ok(ctx.ite(cond, ctx.udiv(then_, &rhs)?, ctx.udiv(else_, rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.udiv(&lhs, then_)?, ctx.udiv(&lhs, else_)?)?)
            } else {
                Ok(ctx.udiv(lhs, rhs)?)
            }
        }
        BitVecOp::SDiv(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(cond, ctx.sdiv(then_, rhs_then)?, ctx.sdiv(then_, rhs_else)?)?)
                } else {
                    Ok(ctx.ite(cond, ctx.sdiv(then_, &rhs)?, ctx.sdiv(else_, rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.sdiv(&lhs, then_)?, ctx.sdiv(lhs, else_)?)?)
            } else {
                Ok(ctx.sdiv(lhs, rhs)?)
            }
        }
        BitVecOp::URem(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(cond, ctx.urem(then_, rhs_then)?, ctx.urem(then_, rhs_else)?)?)
                } else {
                    Ok(ctx.ite(cond, ctx.urem(then_, &rhs)?, ctx.urem(else_, rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.urem(&lhs, then_)?, ctx.urem(lhs, else_)?)?)
            } else {
                Ok(ctx.urem(lhs, rhs)?)
            }
        }
        BitVecOp::SRem(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(cond, ctx.srem(then_, rhs_then)?, ctx.srem(then_, rhs_else)?)?)
                } else {
                    Ok(ctx.ite(cond, ctx.srem(then_, &rhs)?, ctx.srem(else_, rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.srem(&lhs, then_)?, ctx.srem(lhs, else_)?)?)
            } else {
                Ok(ctx.srem(lhs, rhs)?)
            }
        }
        BitVecOp::ShL(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(cond, ctx.shl(then_, rhs_then)?, ctx.shl(then_, rhs_else)?)?)
                } else {
                    Ok(ctx.ite(cond, ctx.shl(then_, &rhs)?, ctx.shl(else_, rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.shl(&lhs, then_)?, ctx.shl(lhs, else_)?)?)
            } else {
                Ok(ctx.shl(lhs, rhs)?)
            }
        }
        BitVecOp::LShR(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(cond, ctx.lshr(then_, rhs_then)?, ctx.lshr(then_, rhs_else)?)?)
                } else {
                    Ok(ctx.ite(cond, ctx.lshr(then_, &rhs)?, ctx.lshr(else_, rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.lshr(&lhs, then_)?, ctx.lshr(lhs, else_)?)?)
            } else {
                Ok(ctx.lshr(lhs, rhs)?)
            }
        }
        BitVecOp::AShR(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(cond, ctx.ashr(then_, rhs_then)?, ctx.ashr(then_, rhs_else)?)?)
                } else {
                    Ok(ctx.ite(cond, ctx.ashr(then_, &rhs)?, ctx.ashr(else_, rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.ashr(&lhs, then_)?, ctx.ashr(lhs, else_)?)?)
            } else {
                Ok(ctx.ashr(lhs, rhs)?)
            }
        }
        BitVecOp::RotateLeft(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.rotate_left(then_, rhs_then)?,
                        ctx.rotate_left(then_, rhs_else)?,
                    )?)
                } else {
                    Ok(ctx.ite(
                        cond,
                        ctx.rotate_left(then_, &rhs)?,
                        ctx.rotate_left(else_, rhs)?,
                    )?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.rotate_left(&lhs, then_)?,
                    ctx.rotate_left(lhs, else_)?,
                )?)
            } else {
                Ok(ctx.rotate_left(lhs, rhs)?)
            }
        }
        BitVecOp::RotateRight(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.rotate_right(then_, rhs_then)?,
                        ctx.rotate_right(then_, rhs_else)?,
                    )?)
                } else {
                    Ok(ctx.ite(
                        cond,
                        ctx.rotate_right(then_, &rhs)?,
                        ctx.rotate_right(else_, rhs)?,
                    )?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.rotate_right(&lhs, then_)?,
                    ctx.rotate_right(lhs, else_)?,
                )?)
            } else {
                Ok(ctx.rotate_right(lhs, rhs)?)
            }
        }
        BitVecOp::ZeroExt(_, amount) => {
            let ast = extract_bitvec_child(children, 0)?;

            if let BitVecOp::ITE(cond, then_, else_) = ast.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.zero_ext(then_, *amount)?,
                    ctx.zero_ext(else_, *amount)?,
                )?)
            } else {
                Ok(ctx.zero_ext(ast, *amount)?)
            }
        }
        BitVecOp::SignExt(_, amount) => {
            let ast = extract_bitvec_child(children, 0)?;

            if let BitVecOp::ITE(cond, then_, else_) = ast.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.sign_ext(then_, *amount)?,
                    ctx.sign_ext(else_, *amount)?,
                )?)
            } else {
                Ok(ctx.sign_ext(ast, *amount)?)
            }
        }
        BitVecOp::Extract(_, ub, lb) => {
            let ast = extract_bitvec_child(children, 0)?;

            if let BitVecOp::ITE(cond, then_, else_) = ast.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.extract(then_, *ub, *lb)?,
                    ctx.extract(else_, *ub, *lb)?,
                )?)
            } else {
                Ok(ctx.extract(ast, *ub, *lb)?)
            }
        }
        BitVecOp::Concat(args) => {
            let excavated_args: Vec<BitVecAst<'c>> = (0..args.len())
                .map(|i| extract_bitvec_child(children, i))
                .collect::<Result<_, _>>()?;

            // Find the first ITE in the args
            let ite_idx = excavated_args
                .iter()
                .position(|arg| matches!(arg.op(), BitVecOp::ITE(..)));

            if let Some(idx) = ite_idx {
                // Clone the condition/then/else before we move excavated_args
                let (cond, then_, else_) = if let BitVecOp::ITE(c, t, e) = excavated_args[idx].op()
                {
                    (c.clone(), t.clone(), e.clone())
                } else {
                    unreachable!()
                };

                // Build then and else branches by substituting the ITE
                let mut then_args = excavated_args.clone();
                then_args[idx] = then_;
                let mut else_args = excavated_args;
                else_args[idx] = else_;

                Ok(ctx.ite(&cond, ctx.concat(then_args)?, ctx.concat(else_args)?)?)
            } else {
                ctx.concat(excavated_args)
            }
        }
        BitVecOp::ByteReverse(..) => {
            let ast = extract_bitvec_child(children, 0)?;

            if let BitVecOp::ITE(cond, then_, else_) = ast.op() {
                Ok(ctx.ite(cond, ctx.byte_reverse(then_)?, ctx.byte_reverse(else_)?)?)
            } else {
                Ok(ctx.byte_reverse(ast)?)
            }
        }
        BitVecOp::FpToIEEEBV(..) => {
            let inner = extract_float_child(children, 0)?;

            if let FloatOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.fp_to_ieeebv(then_)?, ctx.fp_to_ieeebv(else_)?)?)
            } else {
                Ok(ctx.fp_to_ieeebv(inner)?)
            }
        }
        BitVecOp::FpToUBV(_, width, rm) => {
            let width = *width;
            let rm = *rm;
            let inner = extract_float_child(children, 0)?;

            if let FloatOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_to_ubv(then_, width, rm)?,
                    ctx.fp_to_ubv(else_, width, rm)?,
                )?)
            } else {
                Ok(ctx.fp_to_ubv(inner, width, rm)?)
            }
        }
        BitVecOp::FpToSBV(_, width, rm) => {
            let width = *width;
            let rm = *rm;
            let inner = extract_float_child(children, 0)?;

            if let FloatOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.fp_to_sbv(then_, width, rm)?,
                    ctx.fp_to_sbv(else_, width, rm)?,
                )?)
            } else {
                Ok(ctx.fp_to_sbv(inner, width, rm)?)
            }
        }
        BitVecOp::StrLen(..) => {
            let inner = extract_string_child(children, 0)?;

            if let StringOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.str_len(then_)?, ctx.str_len(else_)?)?)
            } else {
                Ok(ctx.str_len(inner)?)
            }
        }
        BitVecOp::StrIndexOf(..) => {
            let base = extract_string_child(children, 0)?;
            let substr = extract_string_child(children, 1)?;
            let offset = extract_bitvec_child(children, 2)?;

            if let StringOp::ITE(cond, then_, else_) = base.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_index_of(then_, &substr, &offset)?,
                    ctx.str_index_of(else_, substr, offset)?,
                )?)
            } else if let StringOp::ITE(cond, then_, else_) = substr.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_index_of(&base, then_, &offset)?,
                    ctx.str_index_of(base, else_, offset)?,
                )?)
            } else if let BitVecOp::ITE(cond, then_, else_) = offset.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_index_of(&base, &substr, then_)?,
                    ctx.str_index_of(base, substr, else_)?,
                )?)
            } else {
                Ok(ctx.str_index_of(base, substr, offset)?)
            }
        }
        BitVecOp::StrToBV(..) => {
            let inner = extract_string_child(children, 0)?;

            if let StringOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.str_to_bv(then_)?, ctx.str_to_bv(else_)?)?)
            } else {
                Ok(ctx.str_to_bv(inner)?)
            }
        }
        BitVecOp::ITE(..) => {
            let cond = extract_bool_child(children, 0)?;
            let then_ = extract_bitvec_child(children, 1)?;
            let else_ = extract_bitvec_child(children, 2)?;

            Ok(ctx.ite(cond, then_, else_)?)
        }
        BitVecOp::Union(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.union(then_, rhs_then)?,
                        ctx.union(then_, rhs_else)?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.union(then_, &rhs)?, ctx.union(else_, rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.union(&lhs, then_)?, ctx.union(lhs, else_)?)?)
            } else {
                Ok(ctx.union(lhs, rhs)?)
            }
        }
        BitVecOp::Intersection(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.intersection(then_, rhs_then)?,
                        ctx.intersection(then_, rhs_else)?,
                    )?)
                } else {
                    Ok(ctx.ite(
                        cond,
                        ctx.intersection(then_, &rhs)?,
                        ctx.intersection(else_, rhs)?,
                    )?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.intersection(&lhs, then_)?,
                    ctx.intersection(lhs, else_)?,
                )?)
            } else {
                Ok(ctx.intersection(lhs, rhs)?)
            }
        }
        BitVecOp::Widen(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.widen(then_, rhs_then)?,
                        ctx.widen(then_, rhs_else)?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.widen(then_, &rhs)?, ctx.widen(else_, rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.widen(&lhs, then_)?, ctx.widen(lhs, else_)?)?)
            } else {
                Ok(ctx.widen(lhs, rhs)?)
            }
        }
    }
}
