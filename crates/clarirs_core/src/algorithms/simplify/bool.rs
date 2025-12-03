use super::SimplifyError;
use crate::prelude::*;

pub(crate) fn simplify_bool<'c>(
    state: &mut super::SimplifyState<'c>,
) -> Result<BoolAst<'c>, SimplifyError<'c>> {
    let ctx = state.expr.context();
    let bool_ast = state.expr.clone().into_bool().unwrap();

    match &bool_ast.op() {
        BooleanOp::BoolS(_) | BooleanOp::BoolV(_) => Ok(bool_ast),
        BooleanOp::Not(..) => {
            let arc = state.get_bool_child(0)?;

            match arc.op() {
                BooleanOp::Not(arc) => Ok(arc.clone()),
                BooleanOp::BoolV(v) => Ok(ctx.boolv(!v)?),
                _ => Ok(ctx.not(&arc)?),
            }
        }
        BooleanOp::And(..) => {
            let (arc, arc1) = (state.get_bool_child(0)?, state.get_bool_child(1)?);

            match (arc.op(), arc1.op()) {
                (BooleanOp::BoolV(lhs), BooleanOp::BoolV(rhs)) => Ok(ctx.boolv(*lhs && *rhs)?),

                (BooleanOp::BoolV(true), v) | (v, BooleanOp::BoolV(true)) => {
                    Ok(ctx.make_bool(v.clone())?)
                }
                (BooleanOp::BoolV(false), _) | (_, BooleanOp::BoolV(false)) => Ok(ctx.false_()?),
                (BooleanOp::Not(lhs), rhs) if lhs.op() == rhs => Ok(ctx.false_()?),
                (lhs, BooleanOp::Not(rhs)) if lhs == rhs.op() => Ok(ctx.false_()?),
                (BooleanOp::Not(lhs), BooleanOp::Not(rhs)) => Ok(ctx.not(&ctx.or(lhs, rhs)?)?),
                _ if arc == arc1 => Ok(arc.clone()),
                _ => Ok(ctx.and(&arc, &arc1)?),
            }
        }
        BooleanOp::Or(..) => {
            let (arc, arc1) = (state.get_bool_child(0)?, state.get_bool_child(1)?);

            match (arc.op(), arc1.op()) {
                (BooleanOp::BoolV(lhs), BooleanOp::BoolV(rhs)) => Ok(ctx.boolv(*lhs || *rhs)?),
                (BooleanOp::BoolV(true), _) | (_, BooleanOp::BoolV(true)) => Ok(ctx.true_()?),
                (BooleanOp::BoolV(false), v) | (v, BooleanOp::BoolV(false)) => {
                    Ok(ctx.make_bool(v.clone())?)
                }
                (BooleanOp::Not(lhs), rhs) if lhs.op() == rhs => Ok(ctx.true_()?),
                (lhs, BooleanOp::Not(rhs)) if lhs == rhs.op() => Ok(ctx.true_()?),
                (BooleanOp::Not(lhs), BooleanOp::Not(rhs)) => Ok(ctx.not(&ctx.and(lhs, rhs)?)?),
                _ if arc == arc1 => Ok(arc.clone()),
                _ => Ok(ctx.or(&arc, &arc1)?),
            }
        }
        BooleanOp::Xor(..) => {
            let (arc, arc1) = (state.get_bool_child(0)?, state.get_bool_child(1)?);

            match (arc.op(), arc1.op()) {
                (BooleanOp::BoolV(lhs), BooleanOp::BoolV(rhs)) => Ok(ctx.boolv(*lhs ^ *rhs)?),
                (BooleanOp::BoolV(true), v) | (v, BooleanOp::BoolV(true)) => {
                    Ok(ctx.not(&ctx.make_bool(v.clone())?)?)
                }
                (BooleanOp::BoolV(false), v) | (v, BooleanOp::BoolV(false)) => {
                    Ok(ctx.make_bool(v.clone())?)
                }
                (BooleanOp::Not(lhs), rhs) if lhs.op() == rhs => Ok(ctx.true_()?),
                (lhs, BooleanOp::Not(rhs)) if lhs == rhs.op() => Ok(ctx.true_()?),
                // ¬a ⊕ ¬b = a ⊕ b (XOR is invariant under double negation)
                (BooleanOp::Not(lhs), BooleanOp::Not(rhs)) => Ok(ctx.xor(lhs, rhs)?),
                _ if arc == arc1 => Ok(ctx.false_()?),
                _ => Ok(ctx.xor(&arc, &arc1)?),
            }
        }
        BooleanOp::BoolEq(..) => {
            let (arc, arc1) = (state.get_bool_child(0)?, state.get_bool_child(1)?);
            match (arc.op(), arc1.op()) {
                (BooleanOp::BoolV(arc), BooleanOp::BoolV(arc1)) => Ok(ctx.boolv(arc == arc1)?),
                (BooleanOp::BoolV(true), v) | (v, BooleanOp::BoolV(true)) => {
                    Ok(ctx.make_bool(v.clone())?)
                }
                (BooleanOp::BoolV(false), v) | (v, BooleanOp::BoolV(false)) => {
                    Ok(ctx.not(&ctx.make_bool(v.clone())?)?)
                }
                _ if arc == arc1 => Ok(ctx.true_()?),
                _ => Ok(ctx.eq_(&arc, &arc1)?),
            }
        }
        BooleanOp::BoolNeq(..) => {
            let (arc, arc1) = (state.get_bool_child(0)?, state.get_bool_child(1)?);
            match (arc.op(), arc1.op()) {
                (BooleanOp::BoolV(arc), BooleanOp::BoolV(arc1)) => Ok(ctx.boolv(arc != arc1)?),
                (BooleanOp::BoolV(true), v) | (v, BooleanOp::BoolV(true)) => {
                    Ok(ctx.not(&ctx.make_bool(v.clone())?)?)
                }
                (BooleanOp::BoolV(false), v) | (v, BooleanOp::BoolV(false)) => {
                    Ok(ctx.make_bool(v.clone())?)
                }
                _ if arc == arc1 => Ok(ctx.false_()?),
                _ => Ok(ctx.neq(&arc, &arc1)?),
            }
        }
        BooleanOp::Eq(..) => {
            let (arc, arc1) = (state.get_bv_child(0)?, state.get_bv_child(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc == arc1)?),

                // General pattern: Eq(If(cond, a, b), a) -> cond (when a != b)
                (BitVecOp::If(cond, then_bv, else_bv), rhs_val) if then_bv.op() == rhs_val => {
                    match (then_bv.op(), else_bv.op()) {
                        (BitVecOp::BVV(then_val), BitVecOp::BVV(else_val))
                            if then_val != else_val =>
                        {
                            Ok(cond.clone())
                        }
                        (then_op, else_op) if then_op != else_op => Ok(cond.clone()),
                        _ => Ok(ctx.eq_(&arc, &arc1)?),
                    }
                }
                // General pattern: Eq(If(cond, a, b), b) -> !cond (when a != b)
                (BitVecOp::If(cond, then_bv, else_bv), rhs_val) if else_bv.op() == rhs_val => {
                    match (then_bv.op(), else_bv.op()) {
                        (BitVecOp::BVV(then_val), BitVecOp::BVV(else_val))
                            if then_val != else_val =>
                        {
                            Ok(ctx.not(cond)?)
                        }
                        (then_op, else_op) if then_op != else_op => Ok(ctx.not(cond)?),
                        _ => Ok(ctx.eq_(&arc, &arc1)?),
                    }
                }
                // Symmetric cases
                (lhs_val, BitVecOp::If(cond, then_bv, else_bv)) if then_bv.op() == lhs_val => {
                    match (then_bv.op(), else_bv.op()) {
                        (BitVecOp::BVV(then_val), BitVecOp::BVV(else_val))
                            if then_val != else_val =>
                        {
                            Ok(cond.clone())
                        }
                        (then_op, else_op) if then_op != else_op => Ok(cond.clone()),
                        _ => Ok(ctx.eq_(&arc, &arc1)?),
                    }
                }
                (lhs_val, BitVecOp::If(cond, then_bv, else_bv)) if else_bv.op() == lhs_val => {
                    match (then_bv.op(), else_bv.op()) {
                        (BitVecOp::BVV(then_val), BitVecOp::BVV(else_val))
                            if then_val != else_val =>
                        {
                            Ok(ctx.not(cond)?)
                        }
                        (then_op, else_op) if then_op != else_op => Ok(ctx.not(cond)?),
                        _ => Ok(ctx.eq_(&arc, &arc1)?),
                    }
                }

                _ => Ok(ctx.eq_(&arc, &arc1)?),
            }
        }
        BooleanOp::Neq(..) => {
            let (arc, arc1) = (state.get_bv_child(0)?, state.get_bv_child(1)?);
            match (arc.op(), arc1.op()) {
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc != arc1)?),
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),

                // General pattern: Neq(If(cond, a, b), b) -> cond (when a != b)
                (BitVecOp::If(cond, then_bv, else_bv), rhs_val) if else_bv.op() == rhs_val => {
                    // Check if then_bv != else_bv
                    match (then_bv.op(), else_bv.op()) {
                        (BitVecOp::BVV(then_val), BitVecOp::BVV(else_val))
                            if then_val != else_val =>
                        {
                            Ok(cond.clone())
                        }
                        (then_op, else_op) if then_op != else_op => Ok(cond.clone()),
                        _ => Ok(ctx.neq(&arc, &arc1)?),
                    }
                }
                // General pattern: Neq(If(cond, a, b), a) -> !cond (when a != b)
                (BitVecOp::If(cond, then_bv, else_bv), rhs_val) if then_bv.op() == rhs_val => {
                    // Check if then_bv != else_bv
                    match (then_bv.op(), else_bv.op()) {
                        (BitVecOp::BVV(then_val), BitVecOp::BVV(else_val))
                            if then_val != else_val =>
                        {
                            Ok(ctx.not(cond)?)
                        }
                        (then_op, else_op) if then_op != else_op => Ok(ctx.not(cond)?),
                        _ => Ok(ctx.neq(&arc, &arc1)?),
                    }
                }
                // Symmetric cases: Neq(b, If(cond, a, b)) -> cond and Neq(a, If(cond, a, b)) -> !cond
                (lhs_val, BitVecOp::If(cond, then_bv, else_bv)) if else_bv.op() == lhs_val => {
                    match (then_bv.op(), else_bv.op()) {
                        (BitVecOp::BVV(then_val), BitVecOp::BVV(else_val))
                            if then_val != else_val =>
                        {
                            Ok(cond.clone())
                        }
                        (then_op, else_op) if then_op != else_op => Ok(cond.clone()),
                        _ => Ok(ctx.neq(&arc, &arc1)?),
                    }
                }
                (lhs_val, BitVecOp::If(cond, then_bv, else_bv)) if then_bv.op() == lhs_val => {
                    match (then_bv.op(), else_bv.op()) {
                        (BitVecOp::BVV(then_val), BitVecOp::BVV(else_val))
                            if then_val != else_val =>
                        {
                            Ok(ctx.not(cond)?)
                        }
                        (then_op, else_op) if then_op != else_op => Ok(ctx.not(cond)?),
                        _ => Ok(ctx.neq(&arc, &arc1)?),
                    }
                }

                _ => Ok(ctx.neq(&arc, &arc1)?),
            }
        }
        BooleanOp::ULT(..) => {
            let (arc, arc1) = (state.get_bv_child(0)?, state.get_bv_child(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc < arc1)?),
                _ => Ok(ctx.ult(&arc, &arc1)?),
            }
        }
        BooleanOp::ULE(..) => {
            let (arc, arc1) = (state.get_bv_child(0)?, state.get_bv_child(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc <= arc1)?),
                _ => Ok(ctx.ule(&arc, &arc1)?),
            }
        }
        BooleanOp::UGT(..) => {
            let (arc, arc1) = (state.get_bv_child(0)?, state.get_bv_child(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc > arc1)?),
                _ => Ok(ctx.ugt(&arc, &arc1)?),
            }
        }
        BooleanOp::UGE(..) => {
            let (arc, arc1) = (state.get_bv_child(0)?, state.get_bv_child(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc >= arc1)?),
                _ => Ok(ctx.uge(&arc, &arc1)?),
            }
        }
        BooleanOp::SLT(..) => {
            let (arc, arc1) = (state.get_bv_child(0)?, state.get_bv_child(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_lt(arc1))?),
                _ => Ok(ctx.slt(&arc, &arc1)?),
            }
        }
        BooleanOp::SLE(..) => {
            let (arc, arc1) = (state.get_bv_child(0)?, state.get_bv_child(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_le(arc1))?),
                _ => Ok(ctx.sle(&arc, &arc1)?),
            }
        }
        BooleanOp::SGT(..) => {
            let (arc, arc1) = (state.get_bv_child(0)?, state.get_bv_child(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.false_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_gt(arc1))?),
                _ => Ok(ctx.sgt(&arc, &arc1)?),
            }
        }
        BooleanOp::SGE(..) => {
            let (arc, arc1) = (state.get_bv_child(0)?, state.get_bv_child(1)?);
            match (arc.op(), arc1.op()) {
                (lhs, rhs) if lhs == rhs => Ok(ctx.true_()?),
                (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => Ok(ctx.boolv(arc.signed_ge(arc1))?),
                _ => Ok(ctx.sge(&arc, &arc1)?),
            }
        }
        BooleanOp::FpEq(..) => {
            let (arc, arc1) = (state.get_fp_child(0)?, state.get_fp_child(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(arc.compare_fp(arc1))?),
                _ => Ok(ctx.fp_eq(&arc, &arc1)?),
            }
        }
        BooleanOp::FpNeq(..) => {
            let (arc, arc1) = (state.get_fp_child(0)?, state.get_fp_child(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(!arc.compare_fp(arc1))?),
                _ => Ok(ctx.fp_neq(&arc, &arc1)?),
            }
        }
        BooleanOp::FpLt(..) => {
            let (arc, arc1) = (state.get_fp_child(0)?, state.get_fp_child(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(arc.lt(arc1))?),
                _ => Ok(ctx.fp_lt(&arc, &arc1)?),
            }
        }
        BooleanOp::FpLeq(..) => {
            let (arc, arc1) = (state.get_fp_child(0)?, state.get_fp_child(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(arc.leq(arc1))?),
                _ => Ok(ctx.fp_leq(&arc, &arc1)?),
            }
        }
        BooleanOp::FpGt(..) => {
            let (arc, arc1) = (state.get_fp_child(0)?, state.get_fp_child(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(arc.gt(arc1))?),
                _ => Ok(ctx.fp_gt(&arc, &arc1)?),
            }
        }
        BooleanOp::FpGeq(..) => {
            let (arc, arc1) = (state.get_fp_child(0)?, state.get_fp_child(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => Ok(ctx.boolv(arc.geq(arc1))?),
                _ => Ok(ctx.fp_geq(&arc, &arc1)?),
            }
        }
        BooleanOp::FpIsNan(..) => {
            let arc = state.get_fp_child(0)?;
            match arc.op() {
                FloatOp::FPV(arc) => Ok(ctx.boolv(arc.is_nan())?),
                _ => Ok(ctx.fp_is_nan(&arc)?),
            }
        }
        BooleanOp::FpIsInf(..) => {
            let arc = state.get_fp_child(0)?;
            match arc.op() {
                FloatOp::FPV(arc) => Ok(ctx.boolv(arc.is_infinity())?),
                _ => Ok(ctx.fp_is_inf(&arc)?),
            }
        }
        BooleanOp::StrContains(..) => {
            let (arc, arc1) = (state.get_string_child(0)?, state.get_string_child(1)?);
            match (arc.op(), arc1.op()) {
                // Check if `input_string` contains `substring`
                (StringOp::StringV(input_string), StringOp::StringV(substring)) => {
                    Ok(ctx.boolv(input_string.contains(substring))?)
                }
                _ => Ok(ctx.strcontains(&arc, &arc1)?),
            }
        }
        BooleanOp::StrPrefixOf(..) => {
            let (arc, arc1) = (state.get_string_child(0)?, state.get_string_child(1)?);
            match (arc.op(), arc1.op()) {
                // Check if `input_string` starts with `prefix substring`
                (StringOp::StringV(prefix), StringOp::StringV(input_string)) => {
                    Ok(ctx.boolv(input_string.starts_with(prefix))?)
                }
                _ => Ok(ctx.strprefixof(&arc, &arc1)?),
            }
        }
        BooleanOp::StrSuffixOf(..) => {
            let (arc, arc1) = (state.get_string_child(0)?, state.get_string_child(1)?);
            match (arc.op(), arc1.op()) {
                // Check if `input_string` ends with `suffix substring`
                (StringOp::StringV(suffix), StringOp::StringV(input_string)) => {
                    Ok(ctx.boolv(input_string.ends_with(suffix))?)
                }
                _ => Ok(ctx.strsuffixof(&arc, &arc1)?),
            }
        }
        BooleanOp::StrIsDigit(..) => {
            let arc = state.get_string_child(0)?;
            match arc.op() {
                StringOp::StringV(input_string) => {
                    if input_string.is_empty() {
                        return Ok(ctx.boolv(false)?);
                    }
                    // is_numeric() is Unicode-aware and will also return true for non-ASCII numeric characters like Z3
                    Ok(ctx.boolv(input_string.chars().all(|c| c.is_numeric()))?)
                }
                _ => Ok(ctx.strisdigit(&arc)?),
            }
        }
        BooleanOp::StrEq(..) => {
            let (arc, arc1) = (state.get_string_child(0)?, state.get_string_child(1)?);
            match (arc.op(), arc1.op()) {
                (StringOp::StringV(str1), StringOp::StringV(str2)) => Ok(ctx.boolv(str1 == str2)?),
                _ => Ok(ctx.streq(&arc, &arc1)?),
            }
        }
        BooleanOp::StrNeq(..) => {
            let (arc, arc1) = (state.get_string_child(0)?, state.get_string_child(1)?);
            match (arc.op(), arc1.op()) {
                (StringOp::StringV(str1), StringOp::StringV(str2)) => Ok(ctx.boolv(str1 != str2)?),
                _ => Ok(ctx.strneq(&arc, &arc1)?),
            }
        }

        BooleanOp::If(..) => {
            let (cond, then_, else_) = (
                state.get_bool_child(0)?,
                state.get_bool_child(1)?,
                state.get_bool_child(2)?,
            );

            match (cond.op(), then_.op(), else_.op()) {
                // Concrete condition cases
                (BooleanOp::BoolV(true), _, _) => Ok(then_.clone()),
                (BooleanOp::BoolV(false), _, _) => Ok(else_.clone()),

                // Same branch cases
                (_, _, _) if then_ == else_ => Ok(then_.clone()),

                // Known then/else cases
                (_, BooleanOp::BoolV(true), BooleanOp::BoolV(false)) => Ok(cond.clone()),
                (_, BooleanOp::BoolV(false), BooleanOp::BoolV(true)) => Ok(ctx.not(&cond)?),

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
                _ => Ok(ctx.if_(&cond, &then_, &else_)?),
            }
        }
    }
}
