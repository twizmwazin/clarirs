use crate::{algorithms::simplify::simplify, prelude::*};

#[allow(unused_variables)]
impl<'c> Simplify<'c> for BoolAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        let ctx = self.context();
        let hash = self.hash();

        ctx.simplification_cache.get_or_insert_with_bool(hash, || {
            match &self.op() {
                BooleanOp::BoolS(name) => ctx.bools(name.clone()),
                BooleanOp::BoolV(value) => ctx.boolv(*value),
                BooleanOp::Not(arc) => {
                    simplify!(arc);
                    match arc.op() {
                        BooleanOp::Not(arc) => Ok(arc.clone()),
                        BooleanOp::BoolV(v) => ctx.boolv(!v),
                        // BitVecOp::BVV(v) => ctx.bvv(!v.clone())?,
                        _ => ctx.not(&arc),
                    }
                }
                BooleanOp::And(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BooleanOp::BoolV(lhs), BooleanOp::BoolV(rhs)) => ctx.boolv(*lhs && *rhs),
                        (BooleanOp::BoolV(true), v) | (v, BooleanOp::BoolV(true)) => {
                            ctx.make_bool(v.clone())
                        }
                        (BooleanOp::BoolV(false), _) | (_, BooleanOp::BoolV(false)) => ctx.false_(),
                        (BooleanOp::Not(lhs), BooleanOp::Not(rhs)) => ctx.not(&ctx.or(lhs, rhs)?),
                        _ if arc == arc1 => Ok(arc),
                        _ => ctx.and(&arc, &arc1),
                    }
                }
                BooleanOp::Or(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BooleanOp::BoolV(lhs), BooleanOp::BoolV(rhs)) => ctx.boolv(*lhs || *rhs),
                        (BooleanOp::BoolV(true), _) | (_, BooleanOp::BoolV(true)) => ctx.true_(),
                        (BooleanOp::BoolV(false), v) | (v, BooleanOp::BoolV(false)) => {
                            ctx.make_bool(v.clone())
                        }
                        (BooleanOp::Not(lhs), BooleanOp::Not(rhs)) => ctx.not(&ctx.and(lhs, rhs)?),
                        _ if arc == arc1 => Ok(arc),
                        _ => ctx.and(&arc, &arc1),
                    }
                }
                BooleanOp::Xor(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BooleanOp::BoolV(lhs), BooleanOp::BoolV(rhs)) => ctx.boolv(*lhs ^ *rhs),
                        (BooleanOp::BoolV(true), v) | (v, BooleanOp::BoolV(true)) => {
                            ctx.not(&ctx.make_bool(v.clone())?)
                        }
                        (BooleanOp::BoolV(false), v) | (v, BooleanOp::BoolV(false)) => {
                            ctx.make_bool(v.clone())
                        }
                        (BooleanOp::Not(lhs), BooleanOp::Not(rhs)) => ctx.not(&ctx.and(lhs, rhs)?),
                        _ if arc == arc1 => ctx.false_(),
                        _ => ctx.and(&arc, &arc1),
                    }
                }
                BooleanOp::BoolEq(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BooleanOp::BoolV(arc), BooleanOp::BoolV(arc1)) => ctx.boolv(arc == arc1),
                        (BooleanOp::BoolV(true), v) | (v, BooleanOp::BoolV(true)) => {
                            ctx.make_bool(v.clone())
                        }
                        (BooleanOp::BoolV(false), v) | (v, BooleanOp::BoolV(false)) => {
                            ctx.not(&ctx.make_bool(v.clone())?)
                        }
                        _ if arc == arc1 => ctx.true_(),
                        _ => ctx.eq_(&arc, &arc1),
                    }
                }
                BooleanOp::BoolNeq(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BooleanOp::BoolV(arc), BooleanOp::BoolV(arc1)) => ctx.boolv(arc != arc1),
                        _ => ctx.neq(&arc, &arc1),
                    }
                }
                BooleanOp::Eq(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (lhs, rhs) if lhs == rhs => ctx.true_(),
                        (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => ctx.boolv(arc == arc1),
                        _ => ctx.eq_(&arc, &arc1),
                    }
                }
                BooleanOp::Neq(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => ctx.boolv(arc != arc1),
                        _ => ctx.neq(&arc, &arc1),
                    }
                }
                BooleanOp::ULT(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (lhs, rhs) if lhs == rhs => ctx.false_(),
                        (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => ctx.boolv(arc < arc1),
                        _ => ctx.ult(&arc, &arc1),
                    }
                }
                BooleanOp::ULE(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (lhs, rhs) if lhs == rhs => ctx.true_(),
                        (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => ctx.boolv(arc <= arc1),
                        _ => ctx.ule(&arc, &arc1),
                    }
                }
                BooleanOp::UGT(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (lhs, rhs) if lhs == rhs => ctx.false_(),
                        (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => ctx.boolv(arc > arc1),
                        _ => ctx.ule(&arc, &arc1),
                    }
                }
                BooleanOp::UGE(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (lhs, rhs) if lhs == rhs => ctx.true_(),
                        (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => ctx.boolv(arc >= arc1),
                        _ => ctx.ule(&arc, &arc1),
                    }
                }
                BooleanOp::SLT(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (lhs, rhs) if lhs == rhs => ctx.false_(),
                        (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => ctx.boolv(arc.signed_lt(arc1)),
                        _ => ctx.slt(&arc, &arc1),
                    }
                }
                BooleanOp::SLE(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (lhs, rhs) if lhs == rhs => ctx.true_(),
                        (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => ctx.boolv(arc.signed_le(arc1)),
                        _ => ctx.sle(&arc, &arc1),
                    }
                }
                BooleanOp::SGT(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (lhs, rhs) if lhs == rhs => ctx.false_(),
                        (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => ctx.boolv(arc.signed_gt(arc1)),
                        _ => ctx.sgt(&arc, &arc1),
                    }
                }
                BooleanOp::SGE(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (lhs, rhs) if lhs == rhs => ctx.true_(),
                        (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => ctx.boolv(arc.signed_ge(arc1)),
                        _ => ctx.sge(&arc, &arc1),
                    }
                }
                BooleanOp::FpEq(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => ctx.boolv(arc.compare_fp(arc1)),
                        _ => ctx.fp_eq(&arc, &arc1),
                    }
                }
                BooleanOp::FpNeq(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => ctx.boolv(!arc.compare_fp(arc1)),
                        _ => ctx.fp_neq(&arc, &arc1),
                    }
                }
                BooleanOp::FpLt(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => ctx.boolv(arc.lt(arc1)),
                        _ => ctx.fp_lt(&arc, &arc1),
                    }
                }
                BooleanOp::FpLeq(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => ctx.boolv(arc.leq(arc1)),
                        _ => ctx.fp_leq(&arc, &arc1),
                    }
                }
                BooleanOp::FpGt(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => ctx.boolv(arc.gt(arc1)),
                        _ => ctx.fp_gt(&arc, &arc1),
                    }
                }
                BooleanOp::FpGeq(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (FloatOp::FPV(arc), FloatOp::FPV(arc1)) => ctx.boolv(arc.geq(arc1)),
                        _ => ctx.fp_geq(&arc, &arc1),
                    }
                }
                BooleanOp::FpIsNan(arc) => {
                    simplify!(arc);
                    match arc.op() {
                        FloatOp::FPV(arc) => ctx.boolv(arc.is_nan()),
                        _ => ctx.fp_is_nan(&arc),
                    }
                }
                BooleanOp::FpIsInf(arc) => {
                    simplify!(arc);
                    match arc.op() {
                        FloatOp::FPV(arc) => ctx.boolv(arc.is_infinity()),
                        _ => ctx.fp_is_inf(&arc),
                    }
                }
                BooleanOp::StrContains(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        // Check if `input_string` contains `substring`
                        (StringOp::StringV(input_string), StringOp::StringV(substring)) => {
                            ctx.boolv(input_string.contains(substring))
                        }
                        _ => ctx.strcontains(&arc, &arc1),
                    }
                }
                BooleanOp::StrPrefixOf(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        // Check if `input_string` starts with `prefix substring`
                        (StringOp::StringV(input_string), StringOp::StringV(prefix)) => {
                            ctx.boolv(input_string.starts_with(prefix))
                        }
                        _ => ctx.strprefixof(&arc, &arc1),
                    }
                }
                BooleanOp::StrSuffixOf(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        // Check if `input_string` ends with `suffix substring`
                        (StringOp::StringV(input_string), StringOp::StringV(suffix)) => {
                            ctx.boolv(input_string.ends_with(suffix))
                        }
                        _ => ctx.strsuffixof(&arc, &arc1),
                    }
                }
                BooleanOp::StrIsDigit(arc) => {
                    simplify!(arc);
                    match arc.op() {
                        StringOp::StringV(input_string) => {
                            ctx.boolv(input_string.chars().all(|c| c.is_ascii_digit()))
                        }
                        _ => ctx.strisdigit(&arc),
                    }
                }
                BooleanOp::StrEq(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (StringOp::StringV(str1), StringOp::StringV(str2)) => {
                            ctx.boolv(str1 == str2)
                        }
                        _ => ctx.streq(&arc, &arc1),
                    }
                }
                BooleanOp::StrNeq(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (StringOp::StringV(str1), StringOp::StringV(str2)) => {
                            ctx.boolv(str1 != str2)
                        }
                        _ => ctx.strneq(&arc, &arc1),
                    }
                }

                BooleanOp::If(cond, then_, else_) => {
                    simplify!(cond, then_, else_);

                    match (cond.op(), then_.op(), else_.op()) {
                        // Concrete condition cases
                        (BooleanOp::BoolV(true), _, _) => Ok(then_.clone()),
                        (BooleanOp::BoolV(false), _, _) => Ok(else_.clone()),

                        // Same branch cases
                        (_, _, _) if then_ == else_ => Ok(then_.clone()),

                        // Known then/else cases
                        (_, BooleanOp::BoolV(true), BooleanOp::BoolV(false)) => Ok(cond.clone()),
                        (_, BooleanOp::BoolV(false), BooleanOp::BoolV(true)) => ctx.not(&cond),

                        // When condition equals one branch with concrete other branch
                        (cond_op, BooleanOp::BoolV(true), else_op) if else_op == cond_op => {
                            Ok(cond.clone())
                        }
                        (cond_op, BooleanOp::BoolV(false), else_op) if else_op == cond_op => {
                            ctx.false_()
                        }
                        (cond_op, then_op, BooleanOp::BoolV(true)) if then_op == cond_op => {
                            ctx.true_()
                        }
                        (cond_op, then_op, BooleanOp::BoolV(false)) if then_op == cond_op => {
                            Ok(cond.clone())
                        }

                        // Default case
                        _ => ctx.if_(&cond, &then_, &else_),
                    }
                }
                BooleanOp::Annotated(arc, annotation) => todo!("bool annotation simplification"),
            }
        })
    }
}
