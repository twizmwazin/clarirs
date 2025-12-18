use super::{extract_bitvec_child, extract_bool_child};
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
        BitVecOp::And(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.bv_and(then_, rhs_then)?,
                            ctx.bv_and(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.bv_and(else_, rhs_then)?,
                            ctx.bv_and(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.bv_and(then_, &rhs)?, ctx.bv_and(else_, rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.bv_and(&lhs, then_)?, ctx.bv_and(lhs, else_)?)?)
            } else {
                Ok(ctx.bv_and(lhs, rhs)?)
            }
        }
        BitVecOp::Or(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.bv_or(then_, rhs_then)?,
                        ctx.bv_or(then_, rhs_else)?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.bv_or(then_, &rhs)?, ctx.bv_or(else_, rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.bv_or(&lhs, then_)?, ctx.bv_or(lhs, else_)?)?)
            } else {
                Ok(ctx.bv_or(lhs, rhs)?)
            }
        }
        BitVecOp::Xor(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(cond, ctx.xor(then_, rhs_then)?, ctx.xor(then_, rhs_else)?)?)
                } else {
                    Ok(ctx.ite(cond, ctx.xor(then_, &rhs)?, ctx.xor(else_, rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.xor(&lhs, then_)?, ctx.xor(lhs, else_)?)?)
            } else {
                Ok(ctx.xor(lhs, rhs)?)
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
        BitVecOp::Add(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(cond, ctx.add(then_, rhs_then)?, ctx.add(then_, rhs_else)?)?)
                } else {
                    Ok(ctx.ite(cond, ctx.add(then_, &rhs)?, ctx.add(else_, rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.add(&lhs, then_)?, ctx.add(lhs, else_)?)?)
            } else {
                Ok(ctx.add(lhs, rhs)?)
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
        BitVecOp::Mul(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(cond, ctx.mul(then_, rhs_then)?, ctx.mul(then_, rhs_else)?)?)
                } else {
                    Ok(ctx.ite(cond, ctx.mul(then_, &rhs)?, ctx.mul(else_, &rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.mul(&lhs, then_)?, ctx.mul(lhs, else_)?)?)
            } else {
                Ok(ctx.mul(lhs, rhs)?)
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
        BitVecOp::Concat(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::ITE(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::ITE(_, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.ite(
                        cond,
                        ctx.concat(then_, rhs_then)?,
                        ctx.concat(then_, rhs_else)?,
                    )?)
                } else {
                    Ok(ctx.ite(cond, ctx.concat(then_, &rhs)?, ctx.concat(else_, rhs)?)?)
                }
            } else if let BitVecOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(cond, ctx.concat(&lhs, then_)?, ctx.concat(lhs, else_)?)?)
            } else {
                Ok(ctx.concat(lhs, rhs)?)
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
        BitVecOp::FpToIEEEBV(..) | BitVecOp::FpToUBV(..) | BitVecOp::FpToSBV(..) => {
            todo!("excavate_ite for float ops")
        }
        BitVecOp::StrLen(..) | BitVecOp::StrIndexOf(..) | BitVecOp::StrToBV(..) => {
            todo!("excavate_ite for string ops")
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
    }
}
