use crate::{
    algorithms::simplify::{extract_bitvec_child, extract_bool_child},
    prelude::*,
};

pub(crate) fn excavate_ite<'c>(
    ast: &BoolAst<'c>,
    children: &[DynAst<'c>],
) -> Result<BoolAst<'c>, ClarirsError> {
    let ctx = ast.context();

    match &ast.op() {
        BooleanOp::BoolS(..) | BooleanOp::BoolV(..) => Ok(ast.clone()),
        BooleanOp::Not(..) => {
            let ast = extract_bool_child(children, 0)?;

            if let BooleanOp::If(cond, then_, else_) = ast.op() {
                Ok(ctx.if_(cond, &ctx.not(then_)?, &ctx.not(else_)?)?)
            } else {
                Ok(ctx.not(&ast)?)
            }
        }
        BooleanOp::And(..) => {
            let lhs = extract_bool_child(children, 0)?;
            let rhs = extract_bool_child(children, 1)?;

            if let BooleanOp::If(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BooleanOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.if_(
                        cond,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.and(then_, rhs_then)?,
                            &ctx.and(then_, rhs_else)?,
                        )?,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.and(else_, rhs_then)?,
                            &ctx.and(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.if_(cond, &ctx.and(then_, &rhs)?, &ctx.and(else_, &rhs)?)?)
                }
            } else if let BooleanOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.if_(cond, &ctx.and(&lhs, then_)?, &ctx.and(&lhs, else_)?)?)
            } else {
                Ok(ctx.and(&lhs, &rhs)?)
            }
        }
        BooleanOp::Or(..) => {
            let lhs = extract_bool_child(children, 0)?;
            let rhs = extract_bool_child(children, 1)?;

            if let BooleanOp::If(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BooleanOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.if_(
                        cond,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.or(then_, rhs_then)?,
                            &ctx.or(then_, rhs_else)?,
                        )?,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.or(else_, rhs_then)?,
                            &ctx.or(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.if_(cond, &ctx.or(then_, &rhs)?, &ctx.or(else_, &rhs)?)?)
                }
            } else if let BooleanOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.if_(cond, &ctx.or(&lhs, then_)?, &ctx.or(&lhs, else_)?)?)
            } else {
                Ok(ctx.or(&lhs, &rhs)?)
            }
        }
        BooleanOp::Xor(..) => {
            let lhs = extract_bool_child(children, 0)?;
            let rhs = extract_bool_child(children, 1)?;

            if let BooleanOp::If(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BooleanOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.if_(
                        cond,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.xor(then_, rhs_then)?,
                            &ctx.xor(then_, rhs_else)?,
                        )?,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.xor(else_, rhs_then)?,
                            &ctx.xor(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.if_(cond, &ctx.xor(then_, &rhs)?, &ctx.xor(else_, &rhs)?)?)
                }
            } else if let BooleanOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.if_(cond, &ctx.xor(&lhs, then_)?, &ctx.xor(&lhs, else_)?)?)
            } else {
                Ok(ctx.xor(&lhs, &rhs)?)
            }
        }
        BooleanOp::BoolEq(..) => {
            let lhs = extract_bool_child(children, 0)?;
            let rhs = extract_bool_child(children, 1)?;

            if let BooleanOp::If(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BooleanOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.if_(
                        cond,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.eq_(then_, rhs_then)?,
                            &ctx.eq_(then_, rhs_else)?,
                        )?,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.eq_(else_, rhs_then)?,
                            &ctx.eq_(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.if_(cond, &ctx.eq_(then_, &rhs)?, &ctx.eq_(else_, &rhs)?)?)
                }
            } else if let BooleanOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.if_(cond, &ctx.eq_(&lhs, then_)?, &ctx.eq_(&lhs, else_)?)?)
            } else {
                Ok(ctx.eq_(&lhs, &rhs)?)
            }
        }
        BooleanOp::BoolNeq(..) => {
            let lhs = extract_bool_child(children, 0)?;
            let rhs = extract_bool_child(children, 1)?;

            if let BooleanOp::If(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BooleanOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.if_(
                        cond,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.neq(then_, rhs_then)?,
                            &ctx.neq(then_, rhs_else)?,
                        )?,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.neq(else_, rhs_then)?,
                            &ctx.neq(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.if_(cond, &ctx.neq(then_, &rhs)?, &ctx.neq(else_, &rhs)?)?)
                }
            } else if let BooleanOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.if_(cond, &ctx.neq(&lhs, then_)?, &ctx.neq(&lhs, else_)?)?)
            } else {
                Ok(ctx.neq(&lhs, &rhs)?)
            }
        }
        BooleanOp::Eq(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::If(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.if_(
                        cond,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.eq_(then_, rhs_then)?,
                            &ctx.eq_(then_, rhs_else)?,
                        )?,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.eq_(else_, rhs_then)?,
                            &ctx.eq_(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.if_(cond, &ctx.eq_(then_, &rhs)?, &ctx.eq_(else_, &rhs)?)?)
                }
            } else if let BitVecOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.if_(cond, &ctx.eq_(&lhs, then_)?, &ctx.eq_(&lhs, else_)?)?)
            } else {
                Ok(ctx.eq_(&lhs, &rhs)?)
            }
        }
        BooleanOp::Neq(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::If(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.if_(
                        cond,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.neq(then_, rhs_then)?,
                            &ctx.neq(then_, rhs_else)?,
                        )?,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.neq(else_, rhs_then)?,
                            &ctx.neq(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.if_(cond, &ctx.neq(then_, &rhs)?, &ctx.neq(else_, &rhs)?)?)
                }
            } else if let BitVecOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.if_(cond, &ctx.neq(&lhs, then_)?, &ctx.neq(&lhs, else_)?)?)
            } else {
                Ok(ctx.neq(&lhs, &rhs)?)
            }
        }
        BooleanOp::ULT(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::If(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.if_(
                        cond,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.ult(then_, rhs_then)?,
                            &ctx.ult(then_, rhs_else)?,
                        )?,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.ult(else_, rhs_then)?,
                            &ctx.ult(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.if_(cond, &ctx.ult(then_, &rhs)?, &ctx.ult(else_, &rhs)?)?)
                }
            } else if let BitVecOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.if_(cond, &ctx.ult(&lhs, then_)?, &ctx.ult(&lhs, else_)?)?)
            } else {
                Ok(ctx.ult(&lhs, &rhs)?)
            }
        }
        BooleanOp::ULE(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::If(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.if_(
                        cond,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.ule(then_, rhs_then)?,
                            &ctx.ule(then_, rhs_else)?,
                        )?,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.ule(else_, rhs_then)?,
                            &ctx.ule(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.if_(cond, &ctx.ule(then_, &rhs)?, &ctx.ule(else_, &rhs)?)?)
                }
            } else if let BitVecOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.if_(cond, &ctx.ule(&lhs, then_)?, &ctx.ule(&lhs, else_)?)?)
            } else {
                Ok(ctx.ule(&lhs, &rhs)?)
            }
        }
        BooleanOp::UGT(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::If(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.if_(
                        cond,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.ugt(then_, rhs_then)?,
                            &ctx.ugt(then_, rhs_else)?,
                        )?,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.ugt(else_, rhs_then)?,
                            &ctx.ugt(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.if_(cond, &ctx.ugt(then_, &rhs)?, &ctx.ugt(else_, &rhs)?)?)
                }
            } else if let BitVecOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.if_(cond, &ctx.ugt(&lhs, then_)?, &ctx.ugt(&lhs, else_)?)?)
            } else {
                Ok(ctx.ugt(&lhs, &rhs)?)
            }
        }
        BooleanOp::UGE(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::If(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.if_(
                        cond,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.uge(then_, rhs_then)?,
                            &ctx.uge(then_, rhs_else)?,
                        )?,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.uge(else_, rhs_then)?,
                            &ctx.uge(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.if_(cond, &ctx.uge(then_, &rhs)?, &ctx.uge(else_, &rhs)?)?)
                }
            } else if let BitVecOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.if_(cond, &ctx.uge(&lhs, then_)?, &ctx.uge(&lhs, else_)?)?)
            } else {
                Ok(ctx.uge(&lhs, &rhs)?)
            }
        }
        BooleanOp::SLT(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::If(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.if_(
                        cond,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.slt(then_, rhs_then)?,
                            &ctx.slt(then_, rhs_else)?,
                        )?,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.slt(else_, rhs_then)?,
                            &ctx.slt(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.if_(cond, &ctx.slt(then_, &rhs)?, &ctx.slt(else_, &rhs)?)?)
                }
            } else if let BitVecOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.if_(cond, &ctx.slt(&lhs, then_)?, &ctx.slt(&lhs, else_)?)?)
            } else {
                Ok(ctx.slt(&lhs, &rhs)?)
            }
        }
        BooleanOp::SLE(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::If(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.if_(
                        cond,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.sle(then_, rhs_then)?,
                            &ctx.sle(then_, rhs_else)?,
                        )?,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.sle(else_, rhs_then)?,
                            &ctx.sle(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.if_(cond, &ctx.sle(then_, &rhs)?, &ctx.sle(else_, &rhs)?)?)
                }
            } else if let BitVecOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.if_(cond, &ctx.sle(&lhs, then_)?, &ctx.sle(&lhs, else_)?)?)
            } else {
                Ok(ctx.sle(&lhs, &rhs)?)
            }
        }
        BooleanOp::SGT(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::If(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.if_(
                        cond,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.sgt(then_, rhs_then)?,
                            &ctx.sgt(then_, rhs_else)?,
                        )?,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.sgt(else_, rhs_then)?,
                            &ctx.sgt(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.if_(cond, &ctx.sgt(then_, &rhs)?, &ctx.sgt(else_, &rhs)?)?)
                }
            } else if let BitVecOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.if_(cond, &ctx.sgt(&lhs, then_)?, &ctx.sgt(&lhs, else_)?)?)
            } else {
                Ok(ctx.sgt(&lhs, &rhs)?)
            }
        }
        BooleanOp::SGE(..) => {
            let lhs = extract_bitvec_child(children, 0)?;
            let rhs = extract_bitvec_child(children, 1)?;

            if let BitVecOp::If(cond, then_, else_) = lhs.op() {
                // Handle case where both sides are If expressions
                if let BitVecOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    // Prioritize left condition as outer if
                    Ok(ctx.if_(
                        cond,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.sge(then_, rhs_then)?,
                            &ctx.sge(then_, rhs_else)?,
                        )?,
                        &ctx.if_(
                            rhs_cond,
                            &ctx.sge(else_, rhs_then)?,
                            &ctx.sge(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.if_(cond, &ctx.sge(then_, &rhs)?, &ctx.sge(else_, &rhs)?)?)
                }
            } else if let BitVecOp::If(cond, then_, else_) = rhs.op() {
                Ok(ctx.if_(cond, &ctx.sge(&lhs, then_)?, &ctx.sge(&lhs, else_)?)?)
            } else {
                Ok(ctx.sge(&lhs, &rhs)?)
            }
        }
        BooleanOp::FpEq(..)
        | BooleanOp::FpNeq(..)
        | BooleanOp::FpLt(..)
        | BooleanOp::FpLeq(..)
        | BooleanOp::FpGt(..)
        | BooleanOp::FpGeq(..)
        | BooleanOp::FpIsNan(..)
        | BooleanOp::FpIsInf(..) => {
            todo!("excavate ite for floating point operations")
        }
        BooleanOp::StrContains(..)
        | BooleanOp::StrPrefixOf(..)
        | BooleanOp::StrSuffixOf(..)
        | BooleanOp::StrIsDigit(..)
        | BooleanOp::StrEq(..)
        | BooleanOp::StrNeq(..) => {
            todo!("excavate ite for string operations")
        }
        BooleanOp::If(..) => {
            let cond = extract_bool_child(children, 0)?;
            let then = extract_bool_child(children, 1)?;
            let else_ = extract_bool_child(children, 2)?;

            Ok(ctx.if_(&cond, &then, &else_)?)
        }
    }
}
