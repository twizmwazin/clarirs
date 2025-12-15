use super::SimplifyError;
use crate::prelude::*;

pub(crate) fn simplify_bool<'c>(
    state: &mut super::SimplifyState<'c>,
) -> Result<BoolAst<'c>, SimplifyError<'c>> {
    let ctx = state.expr.context();
    let bool_ast = state.expr.clone().into_bool().unwrap();

    match bool_ast.op() {
        BooleanOp::BoolS(_) | BooleanOp::BoolV(_) => Ok(bool_ast),
        BooleanOp::Not(..) => {
            let arc = state.get_bool_simplified(0)?;

            match arc.op() {
                BooleanOp::Not(arc) => Ok(arc.clone()),
                BooleanOp::BoolV(v) => Ok(ctx.boolv(!v)?),

                BooleanOp::Eq(lhs, rhs) => Ok(ctx.neq(lhs.clone(), rhs.clone())?),

                // !(a > b)  ==>  a <= b
                BooleanOp::UGT(lhs, rhs) => state.rerun(ctx.ule(lhs.clone(), rhs.clone())?),
                // !(a >= b)  ==>  a < b
                BooleanOp::UGE(lhs, rhs) => state.rerun(ctx.ult(lhs.clone(), rhs.clone())?),
                // !(a < b)  ==>  a >= b
                BooleanOp::ULT(lhs, rhs) => state.rerun(ctx.uge(lhs.clone(), rhs.clone())?),
                // !(a <= b)  ==>  a > b
                BooleanOp::ULE(lhs, rhs) => state.rerun(ctx.ugt(lhs.clone(), rhs.clone())?),
                // !(a s> b)  ==>  a s<= b
                BooleanOp::SGT(lhs, rhs) => state.rerun(ctx.sle(lhs.clone(), rhs.clone())?),
                // !(a s>= b)  ==>  a s< b
                BooleanOp::SGE(lhs, rhs) => state.rerun(ctx.slt(lhs.clone(), rhs.clone())?),
                // !(a s< b)  ==>  a s>= b
                BooleanOp::SLT(lhs, rhs) => state.rerun(ctx.sge(lhs.clone(), rhs.clone())?),
                // !(a s<= b)  ==>  a s> b
                BooleanOp::SLE(lhs, rhs) => state.rerun(ctx.sgt(lhs.clone(), rhs.clone())?),

                _ => Ok(ctx.not(arc)?),
            }
        }
        BooleanOp::And(..) => {
            let early_lhs = state.get_bool_available(0)?;
            let early_rhs = state.get_bool_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (BooleanOp::BoolV(lhs), BooleanOp::BoolV(rhs)) => Ok(ctx.boolv(*lhs && *rhs)?),
                (BooleanOp::BoolV(true), _) => Ok(state.get_bool_simplified(1)?),
                (_, BooleanOp::BoolV(true)) => Ok(state.get_bool_simplified(0)?),
                (BooleanOp::BoolV(false), _) | (_, BooleanOp::BoolV(false)) => Ok(ctx.false_()?),
                (BooleanOp::Not(lhs), rhs) if lhs.op() == rhs => Ok(ctx.false_()?),
                (lhs, BooleanOp::Not(rhs)) if lhs == rhs.op() => Ok(ctx.false_()?),
                (BooleanOp::Not(lhs), BooleanOp::Not(rhs)) => Ok(ctx.not(ctx.or(lhs, rhs)?)?),
                _ if early_lhs == early_rhs => state.get_bool_simplified(0),
                _ => Ok(ctx.and(state.get_bool_simplified(0)?, state.get_bool_simplified(1)?)?),
            }
        }
        BooleanOp::Or(..) => {
            let early_lhs = state.get_bool_available(0)?;
            let early_rhs = state.get_bool_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (BooleanOp::BoolV(lhs), BooleanOp::BoolV(rhs)) => Ok(ctx.boolv(*lhs || *rhs)?),
                (BooleanOp::BoolV(true), _) | (_, BooleanOp::BoolV(true)) => Ok(ctx.true_()?),
                (BooleanOp::BoolV(false), _) => Ok(state.get_bool_simplified(1)?),
                (_, BooleanOp::BoolV(false)) => Ok(state.get_bool_simplified(0)?),
                (BooleanOp::Not(lhs), rhs) if lhs.op() == rhs => Ok(ctx.true_()?),
                (lhs, BooleanOp::Not(rhs)) if lhs == rhs.op() => Ok(ctx.true_()?),
                (BooleanOp::Not(lhs), BooleanOp::Not(rhs)) => Ok(ctx.not(ctx.and(lhs, rhs)?)?),
                _ if early_lhs == early_rhs => state.get_bool_simplified(0),

                // x == K || x >= K  ==>  x >= K
                (BooleanOp::Eq(var1, val1), BooleanOp::UGE(var2, val2))
                | (BooleanOp::UGE(var2, val2), BooleanOp::Eq(var1, val1))
                    if var1 == var2 && val1 == val2 =>
                {
                    state.rerun(ctx.uge(var1.clone(), val1.clone())?)
                }
                // x == K || x > K  ==>  x >= K
                (BooleanOp::Eq(var1, val1), BooleanOp::UGT(var2, val2))
                | (BooleanOp::UGT(var2, val2), BooleanOp::Eq(var1, val1))
                    if var1 == var2 && val1 == val2 =>
                {
                    state.rerun(ctx.uge(var1.clone(), val1.clone())?)
                }
                // x == K || x <= K  ==>  x <= K
                (BooleanOp::Eq(var1, val1), BooleanOp::ULE(var2, val2))
                | (BooleanOp::ULE(var2, val2), BooleanOp::Eq(var1, val1))
                    if var1 == var2 && val1 == val2 =>
                {
                    state.rerun(ctx.ule(var1.clone(), val1.clone())?)
                }
                // x == K || x < K  ==>  x <= K
                (BooleanOp::Eq(var1, val1), BooleanOp::ULT(var2, val2))
                | (BooleanOp::ULT(var2, val2), BooleanOp::Eq(var1, val1))
                    if var1 == var2 && val1 == val2 =>
                {
                    state.rerun(ctx.ule(var1.clone(), val1.clone())?)
                }
                // x == K || x s>= K  ==>  x s>= K
                (BooleanOp::Eq(var1, val1), BooleanOp::SGE(var2, val2))
                | (BooleanOp::SGE(var2, val2), BooleanOp::Eq(var1, val1))
                    if var1 == var2 && val1 == val2 =>
                {
                    state.rerun(ctx.sge(var1.clone(), val1.clone())?)
                }
                // x == K || x s> K  ==>  x s>= K
                (BooleanOp::Eq(var1, val1), BooleanOp::SGT(var2, val2))
                | (BooleanOp::SGT(var2, val2), BooleanOp::Eq(var1, val1))
                    if var1 == var2 && val1 == val2 =>
                {
                    state.rerun(ctx.sge(var1.clone(), val1.clone())?)
                }
                // x == K || x s<= K  ==>  x s<= K
                (BooleanOp::Eq(var1, val1), BooleanOp::SLE(var2, val2))
                | (BooleanOp::SLE(var2, val2), BooleanOp::Eq(var1, val1))
                    if var1 == var2 && val1 == val2 =>
                {
                    state.rerun(ctx.sle(var1.clone(), val1.clone())?)
                }
                // x == K || x s< K  ==>  x s<= K
                (BooleanOp::Eq(var1, val1), BooleanOp::SLT(var2, val2))
                | (BooleanOp::SLT(var2, val2), BooleanOp::Eq(var1, val1))
                    if var1 == var2 && val1 == val2 =>
                {
                    state.rerun(ctx.sle(var1.clone(), val1.clone())?)
                }

                // x <= K || x > K  ==>  true
                (BooleanOp::ULE(var1, val1), BooleanOp::UGT(var2, val2))
                | (BooleanOp::UGT(var2, val2), BooleanOp::ULE(var1, val1))
                    if var1 == var2 && val1 == val2 =>
                {
                    Ok(ctx.true_()?)
                }
                // x < K || x >= K  ==>  true
                (BooleanOp::ULT(var1, val1), BooleanOp::UGE(var2, val2))
                | (BooleanOp::UGE(var2, val2), BooleanOp::ULT(var1, val1))
                    if var1 == var2 && val1 == val2 =>
                {
                    Ok(ctx.true_()?)
                }
                // x <= K || x > K  ==>  true
                (BooleanOp::SLE(var1, val1), BooleanOp::SGT(var2, val2))
                | (BooleanOp::SGT(var2, val2), BooleanOp::SLE(var1, val1))
                    if var1 == var2 && val1 == val2 =>
                {
                    Ok(ctx.true_()?)
                }
                // x < K || x >= K  ==>  true
                (BooleanOp::SLT(var1, val1), BooleanOp::SGE(var2, val2))
                | (BooleanOp::SGE(var2, val2), BooleanOp::SLT(var1, val1))
                    if var1 == var2 && val1 == val2 =>
                {
                    Ok(ctx.true_()?)
                }

                _ => Ok(ctx.or(state.get_bool_simplified(0)?, state.get_bool_simplified(1)?)?),
            }
        }
        BooleanOp::Xor(..) => {
            let early_lhs = state.get_bool_available(0)?;
            let early_rhs = state.get_bool_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (BooleanOp::BoolV(lhs), BooleanOp::BoolV(rhs)) => Ok(ctx.boolv(*lhs ^ *rhs)?),
                (BooleanOp::BoolV(true), _) => Ok(ctx.not(state.get_bool_simplified(1)?)?),
                (_, BooleanOp::BoolV(true)) => Ok(ctx.not(state.get_bool_simplified(0)?)?),
                (BooleanOp::BoolV(false), _) => Ok(state.get_bool_simplified(1)?),
                (_, BooleanOp::BoolV(false)) => Ok(state.get_bool_simplified(0)?),
                (BooleanOp::Not(lhs), rhs) if lhs.op() == rhs => Ok(ctx.true_()?),
                (lhs, BooleanOp::Not(rhs)) if lhs == rhs.op() => Ok(ctx.true_()?),
                (BooleanOp::Not(lhs), BooleanOp::Not(rhs)) => state.rerun(ctx.xor(lhs, rhs)?),
                _ if early_lhs == early_rhs => Ok(ctx.false_()?),
                _ => Ok(ctx.xor(state.get_bool_simplified(0)?, state.get_bool_simplified(1)?)?),
            }
        }
        BooleanOp::BoolEq(..) => {
            let early_lhs = state.get_bool_available(0)?;
            let early_rhs = state.get_bool_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (BooleanOp::BoolV(arc), BooleanOp::BoolV(arc1)) => Ok(ctx.boolv(arc == arc1)?),
                (BooleanOp::BoolV(true), _) => Ok(state.get_bool_simplified(1)?),
                (_, BooleanOp::BoolV(true)) => Ok(state.get_bool_simplified(0)?),
                (BooleanOp::BoolV(false), _) => Ok(ctx.not(state.get_bool_simplified(1)?)?),
                (_, BooleanOp::BoolV(false)) => Ok(ctx.not(state.get_bool_simplified(0)?)?),
                _ if early_lhs == early_rhs => Ok(ctx.true_()?),
                _ => Ok(ctx.eq_(state.get_bool_simplified(0)?, state.get_bool_simplified(1)?)?),
            }
        }
        BooleanOp::BoolNeq(..) => {
            let early_lhs = state.get_bool_available(0)?;
            let early_rhs = state.get_bool_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (BooleanOp::BoolV(arc), BooleanOp::BoolV(arc1)) => Ok(ctx.boolv(arc != arc1)?),
                (BooleanOp::BoolV(true), _) => Ok(ctx.not(state.get_bool_simplified(1)?)?),
                (_, BooleanOp::BoolV(true)) => Ok(ctx.not(state.get_bool_simplified(0)?)?),
                (BooleanOp::BoolV(false), _) => Ok(state.get_bool_simplified(1)?),
                (_, BooleanOp::BoolV(false)) => Ok(state.get_bool_simplified(0)?),
                _ if early_lhs == early_rhs => Ok(ctx.false_()?),
                _ => Ok(ctx.neq(state.get_bool_simplified(0)?, state.get_bool_simplified(1)?)?),
            }
        }
        BooleanOp::Eq(..) => {
            let early_lhs = state.get_bv_available(0)?;
            let early_rhs = state.get_bv_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc == arc1)?),
                _ => Ok(ctx.eq_(state.get_bv_simplified(0)?, state.get_bv_simplified(1)?)?),
            }
        }
        BooleanOp::Neq(..) => {
            let early_lhs = state.get_bv_available(0)?;
            let early_rhs = state.get_bv_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc != arc1)?),
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                _ => Ok(ctx.neq(state.get_bv_simplified(0)?, state.get_bv_simplified(1)?)?),
            }
        }
        BooleanOp::ULT(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc < arc1)?),
                _ => Ok(ctx.ult(arc, arc1)?),
            }
        }
        BooleanOp::ULE(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc <= arc1)?),
                _ => Ok(ctx.ule(arc, arc1)?),
            }
        }
        BooleanOp::UGT(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc > arc1)?),
                _ => Ok(ctx.ugt(arc, arc1)?),
            }
        }
        BooleanOp::UGE(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc >= arc1)?),
                _ => Ok(ctx.uge(arc, arc1)?),
            }
        }
        BooleanOp::SLT(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_lt(arc1))?),
                _ => Ok(ctx.slt(arc, arc1)?),
            }
        }
        BooleanOp::SLE(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_le(arc1))?),
                _ => Ok(ctx.sle(arc, arc1)?),
            }
        }
        BooleanOp::SGT(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_gt(arc1))?),
                _ => Ok(ctx.sgt(arc, arc1)?),
            }
        }
        BooleanOp::SGE(..) => {
            let (arc, arc1) = (state.get_bv_simplified(0)?, state.get_bv_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_ge(arc1))?),
                _ => Ok(ctx.sge(arc, arc1)?),
            }
        }
        BooleanOp::FpEq(..) => {
            let early_lhs = state.get_fp_available(0)?;
            let early_rhs = state.get_fp_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(arc.compare_fp(arc1))?),
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                _ => Ok(ctx.fp_eq(state.get_fp_simplified(0)?, state.get_fp_simplified(1)?)?),
            }
        }
        BooleanOp::FpNeq(..) => {
            let early_lhs = state.get_fp_available(0)?;
            let early_rhs = state.get_fp_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(!arc.compare_fp(arc1))?),
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                _ => Ok(ctx.fp_neq(state.get_fp_simplified(0)?, state.get_fp_simplified(1)?)?),
            }
        }
        BooleanOp::FpLt(..) => {
            let (arc, arc1) = (state.get_fp_simplified(0)?, state.get_fp_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(arc.lt(arc1))?),
                _ => Ok(ctx.fp_lt(arc, arc1)?),
            }
        }
        BooleanOp::FpLeq(..) => {
            let (arc, arc1) = (state.get_fp_simplified(0)?, state.get_fp_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(arc.leq(arc1))?),
                _ => Ok(ctx.fp_leq(arc, arc1)?),
            }
        }
        BooleanOp::FpGt(..) => {
            let (arc, arc1) = (state.get_fp_simplified(0)?, state.get_fp_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(arc.gt(arc1))?),
                _ => Ok(ctx.fp_gt(arc, arc1)?),
            }
        }
        BooleanOp::FpGeq(..) => {
            let (arc, arc1) = (state.get_fp_simplified(0)?, state.get_fp_simplified(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(arc.geq(arc1))?),
                _ => Ok(ctx.fp_geq(arc, arc1)?),
            }
        }
        BooleanOp::FpIsNan(..) => {
            let arc = state.get_fp_simplified(0)?;
            match arc.op() {
                FloatOp::FPV(arc) => Ok(ctx.boolv(arc.is_nan())?),
                _ => Ok(ctx.fp_is_nan(arc)?),
            }
        }
        BooleanOp::FpIsInf(..) => {
            let arc = state.get_fp_simplified(0)?;
            match arc.op() {
                FloatOp::FPV(arc) => Ok(ctx.boolv(arc.is_infinity())?),
                _ => Ok(ctx.fp_is_inf(arc)?),
            }
        }
        BooleanOp::StrContains(..) => {
            let (arc, arc1) = (
                state.get_string_simplified(0)?,
                state.get_string_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                // Check if `input_string` contains `substring`
                (StringOp::StringV(input_string), StringOp::StringV(substring)) => {
                    Ok(ctx.boolv(input_string.contains(substring))?)
                }
                _ => Ok(ctx.strcontains(arc, arc1)?),
            }
        }
        BooleanOp::StrPrefixOf(..) => {
            let (arc, arc1) = (
                state.get_string_simplified(0)?,
                state.get_string_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                // Check if `input_string` starts with `prefix substring`
                (StringOp::StringV(prefix), StringOp::StringV(input_string)) => {
                    Ok(ctx.boolv(input_string.starts_with(prefix))?)
                }
                _ => Ok(ctx.strprefixof(arc, arc1)?),
            }
        }
        BooleanOp::StrSuffixOf(..) => {
            let (arc, arc1) = (
                state.get_string_simplified(0)?,
                state.get_string_simplified(1)?,
            );
            match (arc.op(), arc1.op()) {
                // Check if `input_string` ends with `suffix substring`
                (StringOp::StringV(suffix), StringOp::StringV(input_string)) => {
                    Ok(ctx.boolv(input_string.ends_with(suffix))?)
                }
                _ => Ok(ctx.strsuffixof(arc, arc1)?),
            }
        }
        BooleanOp::StrIsDigit(..) => {
            let arc = state.get_string_simplified(0)?;
            match arc.op() {
                StringOp::StringV(input_string) => {
                    if input_string.is_empty() {
                        return Ok(ctx.boolv(false)?);
                    }
                    // is_numeric() is Unicode-aware and will also return true for non-ASCII numeric characters like Z3
                    Ok(ctx.boolv(input_string.chars().all(|c| c.is_numeric()))?)
                }
                _ => Ok(ctx.strisdigit(arc)?),
            }
        }
        BooleanOp::StrEq(..) => {
            let early_lhs = state.get_string_available(0)?;
            let early_rhs = state.get_string_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (StringOp::StringV(str1), StringOp::StringV(str2)) => Ok(ctx.boolv(str1 == str2)?),
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                _ => Ok(ctx.streq(
                    state.get_string_simplified(0)?,
                    state.get_string_simplified(1)?,
                )?),
            }
        }
        BooleanOp::StrNeq(..) => {
            let early_lhs = state.get_string_available(0)?;
            let early_rhs = state.get_string_available(1)?;

            match (early_lhs.op(), early_rhs.op()) {
                (StringOp::StringV(str1), StringOp::StringV(str2)) => Ok(ctx.boolv(str1 != str2)?),
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                _ => Ok(ctx.strneq(
                    state.get_string_simplified(0)?,
                    state.get_string_simplified(1)?,
                )?),
            }
        }

        BooleanOp::If(..) => {
            let cond = state.get_bool_simplified(0)?;
            let early_then = state.get_bool_available(1)?;
            let early_else = state.get_bool_available(2)?;

            match (cond.op(), early_then.op(), early_else.op()) {
                // Concrete condition cases
                (BooleanOp::BoolV(true), _, _) => state.get_bool_simplified(1),
                (BooleanOp::BoolV(false), _, _) => state.get_bool_simplified(2),

                // Same branch cases
                (_, _, _) if early_then == early_else => state.get_bool_simplified(1),

                // Known then/else cases
                (_, BooleanOp::BoolV(true), BooleanOp::BoolV(false)) => Ok(cond.clone()),
                (_, BooleanOp::BoolV(false), BooleanOp::BoolV(true)) => Ok(ctx.not(cond)?),

                // When condition equals one branch with concrete other branch
                (cond_op, BooleanOp::BoolV(true), else_op) if else_op == cond_op => {
                    Ok(cond.clone())
                }
                (cond_op, BooleanOp::BoolV(false), else_op) if else_op == cond_op => {
                    Ok(ctx.false_()?)
                }
                (cond_op, then_op, BooleanOp::BoolV(true)) if then_op == cond_op => {
                    Ok(ctx.true_()?)
                }
                (cond_op, then_op, BooleanOp::BoolV(false)) if then_op == cond_op => {
                    Ok(cond.clone())
                }

                // Default case
                _ => Ok(ctx.if_(
                    cond,
                    state.get_bool_simplified(1)?,
                    state.get_bool_simplified(2)?,
                )?),
            }
        }
    }
}
