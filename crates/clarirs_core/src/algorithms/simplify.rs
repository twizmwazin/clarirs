use crate::ast::bitvec::BitVecExt;
use crate::prelude::*;
use clarirs_num::*;
use num_bigint::{BigInt, BigUint};
use num_traits::Num;
use num_traits::One;
use num_traits::Zero;

macro_rules! simplify {
    ($($var:ident),*) => {
        $(let $var = $var.simplify()?;)*
    };
}

pub trait Simplify<'c>: Sized {
    fn simplify(&self) -> Result<Self, ClarirsError>;
}

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
                        _ => ctx.ule(&arc, &arc1),
                    }
                }
                BooleanOp::SLE(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (lhs, rhs) if lhs == rhs => ctx.true_(),
                        (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => ctx.boolv(arc.signed_le(arc1)),
                        _ => ctx.ule(&arc, &arc1),
                    }
                }
                BooleanOp::SGT(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (lhs, rhs) if lhs == rhs => ctx.false_(),
                        (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => ctx.boolv(arc.signed_gt(arc1)),
                        _ => ctx.ule(&arc, &arc1),
                    }
                }
                BooleanOp::SGE(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (lhs, rhs) if lhs == rhs => ctx.true_(),
                        (BitVecOp::BVV(arc), BitVecOp::BVV(arc1)) => ctx.boolv(arc.signed_ge(arc1)),
                        _ => ctx.ule(&arc, &arc1),
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
                BooleanOp::Annotated(arc, annotation) => todo!(),
            }
        })
    }
}

#[allow(unused_variables)]
impl<'c> Simplify<'c> for BitVecAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        let ctx = self.context();
        let hash = self.hash();

        ctx.simplification_cache.get_or_insert_with_bv(hash, || {
            match &self.op() {
                BitVecOp::BVS(name, width) => ctx.bvs(name.clone(), *width),
                BitVecOp::BVV(_) => Ok(self.clone()),
                BitVecOp::Not(ast) => {
                    simplify!(ast);
                    match ast.op() {
                        BitVecOp::BVV(value) => ctx.bvv(!value.clone()),
                        _ => ctx.not(&ast),
                    }
                }
                BitVecOp::And(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            ctx.bvv(value1.clone() & value2.clone())
                        }
                        _ => ctx.and(&arc, &arc1),
                    }
                }
                BitVecOp::Or(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            ctx.bvv(value1.clone() | value2.clone())
                        }
                        _ => ctx.or(&arc, &arc1),
                    }
                }
                BitVecOp::Xor(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            ctx.bvv(value1.clone() ^ value2.clone())
                        }
                        _ => ctx.xor(&arc, &arc1),
                    }
                }
                BitVecOp::Abs(arc) => {
                    simplify!(arc);
                    match arc.op() {
                        BitVecOp::BVV(value) => {
                            // Check if the value is negative by examining the sign bit
                            if value.sign() {
                                // If negative, return the negated value
                                ctx.bvv(-value.clone())
                            } else {
                                // If positive, return the value as-is
                                ctx.bvv(value.clone())
                            }
                        }
                        _ => ctx.abs(&arc),
                    }
                }
                BitVecOp::Add(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            ctx.bvv(value1.clone() + value2.clone())
                        }
                        _ => ctx.and(&arc, &arc1),
                    }
                }
                BitVecOp::Sub(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            ctx.bvv(value1.clone() - value2.clone())
                        }
                        _ => ctx.sub(&arc, &arc1),
                    }
                }
                BitVecOp::Mul(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            ctx.bvv(value1.clone() * value2.clone())
                        }
                        _ => ctx.mul(&arc, &arc1),
                    }
                }
                BitVecOp::UDiv(arc, arc1) => {
                    simplify!(arc, arc1);

                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            // Perform unsigned division
                            let quotient = BitVec::from_biguint_trunc(
                                &(value1.to_biguint() / value2.to_biguint()),
                                value1.len(),
                            );
                            ctx.bvv(quotient)
                        }
                        _ => ctx.udiv(&arc, &arc1),
                    }
                }
                BitVecOp::SDiv(arc, arc1) => {
                    simplify!(arc, arc1);

                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            // Convert `value1` and `value2` to `BigInt` to handle signed division
                            let signed_value1 = BigInt::from(value1.to_biguint());
                            let signed_value2 = BigInt::from(value2.to_biguint());

                            // Perform signed division
                            let signed_quotient = signed_value1 / signed_value2;

                            // Convert the result back to `BitVec` and ensure it fits within the original bit length
                            let result_bitvec = BitVec::from_biguint_trunc(
                                &signed_quotient.to_biguint().unwrap(),
                                value1.len(),
                            );
                            ctx.bvv(result_bitvec)
                        }
                        _ => ctx.sdiv(&arc, &arc1),
                    }
                }
                BitVecOp::URem(arc, arc1) => {
                    simplify!(arc, arc1);

                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            // Perform unsigned remainder
                            let remainder = BitVec::from_biguint_trunc(
                                &(value1.to_biguint() % value2.to_biguint()),
                                value1.len(),
                            );
                            ctx.bvv(remainder)
                        }
                        _ => ctx.urem(&arc, &arc1),
                    }
                }
                BitVecOp::SRem(arc, arc1) => {
                    simplify!(arc, arc1);

                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            let unsigned_remainder = value1.to_biguint() % value2.to_biguint();

                            // Check the sign of the dividend (value1)
                            let is_negative = value1.sign();

                            // Convert unsigned remainder to signed form if dividend is negative
                            let remainder = if is_negative {
                                // Negate the remainder
                                -BitVec::from_biguint_trunc(&unsigned_remainder, value1.len())
                            } else {
                                BitVec::from_biguint_trunc(&unsigned_remainder, value1.len())
                            };

                            ctx.bvv(remainder)
                        }
                        _ => ctx.srem(&arc, &arc1),
                    }
                }
                BitVecOp::Pow(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(base), BitVecOp::BVV(exp)) => ctx.bvv(base.pow(exp)?),
                        _ => ctx.pow(&arc, &arc1),
                    }
                }

                BitVecOp::ShL(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value), BitVecOp::BVV(shift_amount)) => {
                            let shift_amount_usize = shift_amount.to_usize().unwrap_or(0);
                            let result = value.clone() << shift_amount_usize;
                            ctx.bvv(result)
                        }
                        _ => ctx.shl(&arc, &arc1),
                    }
                }
                BitVecOp::LShR(arc, arc1) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value), BitVecOp::BVV(shift_amount)) => {
                            let bit_width = value.len();
                            let shift_amount_usize = shift_amount.to_usize().unwrap_or(0);

                            let result = if shift_amount_usize >= bit_width {
                                BitVec::zeros(bit_width)
                            } else if shift_amount_usize == 0 {
                                value.clone()
                            } else {
                                value.clone() >> shift_amount_usize
                            };
                            ctx.bvv(result)
                        }
                        _ => ctx.lshr(&arc, &arc1),
                    }
                }

                BitVecOp::AShR(arc, arc1) => {
                    simplify!(arc, arc1);

                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value), BitVecOp::BVV(shift_amount)) => {
                            let shift_amount_usize = shift_amount.to_usize().unwrap_or(0);
                            let bit_length = value.len();

                            // Convert value to BigUint
                            let unsigned_value = value.to_biguint();

                            // Check sign bit
                            let sign_bit_set = (unsigned_value.clone() >> (bit_length - 1))
                                & BigUint::one()
                                != BigUint::zero();

                            // If shifting >= bit_length, return all-ones (if negative) or all-zeros (if positive)
                            if shift_amount_usize >= bit_length {
                                return if sign_bit_set {
                                    ctx.bvv(BitVec::from_biguint_trunc(
                                        &((BigUint::one() << bit_length) - BigUint::one()),
                                        bit_length,
                                    ))
                                } else {
                                    ctx.bvv(BitVec::zeros(bit_length))
                                };
                            }

                            // Perform the shift
                            let unsigned_shifted = unsigned_value.clone() >> shift_amount_usize;

                            // Extend the sign bit if needed
                            let result = if sign_bit_set {
                                // Create a mask to extend the sign bit
                                let mask = ((BigUint::one() << shift_amount_usize)
                                    - BigUint::one())
                                    << (bit_length - shift_amount_usize);
                                unsigned_shifted | mask
                            } else {
                                unsigned_shifted
                            };

                            ctx.bvv(BitVec::from_biguint_trunc(&result, bit_length))
                        }
                        _ => ctx.ashr(&arc, &arc1),
                    }
                }

                BitVecOp::RotateLeft(arc, arc1) => {
                    simplify!(arc, arc1);

                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value), BitVecOp::BVV(rotate_amount)) => {
                            let rotate_amount_usize =
                                rotate_amount.to_usize().unwrap_or(0) % value.len();
                            let bit_length = value.len();

                            // Rotate left by shifting left and filling in from the right
                            let rotated_value = (value.clone() << rotate_amount_usize)
                                | (value.clone() >> (bit_length - rotate_amount_usize));

                            ctx.bvv(rotated_value)
                        }
                        _ => ctx.rotate_left(&arc, &arc1),
                    }
                }
                BitVecOp::RotateRight(arc, arc1) => {
                    simplify!(arc, arc1);

                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value), BitVecOp::BVV(rotate_amount)) => {
                            let rotate_amount_usize =
                                rotate_amount.to_usize().unwrap_or(0) % value.len();
                            let bit_length = value.len();

                            // Rotate right by shifting right and filling in from the left
                            let rotated_value = (value.clone() >> rotate_amount_usize)
                                | (value.clone() << (bit_length - rotate_amount_usize));

                            ctx.bvv(rotated_value)
                        }
                        _ => ctx.rotate_right(&arc, &arc1),
                    }
                }
                BitVecOp::ZeroExt(arc, num_bits) => {
                    simplify!(arc);

                    match arc.op() {
                        BitVecOp::BVV(value) => ctx.bvv(value.zero_extend(*num_bits as usize)),
                        _ => ctx.zero_ext(&arc, *num_bits),
                    }
                }
                BitVecOp::SignExt(arc, num_bits) => {
                    simplify!(arc);
                    match arc.op() {
                        BitVecOp::BVV(value) => ctx.bvv(value.sign_extend(*num_bits as usize)),
                        _ => ctx.sign_ext(&arc, *num_bits),
                    }
                }
                BitVecOp::Extract(arc, f, t) => {
                    simplify!(arc);

                    // If the extract bounds are the entire BV, return the inner value as-is
                    if *f == 0 && *t == arc.size() - 1 {
                        return Ok(arc);
                    }

                    match arc.op() {
                        // Concrete BVV case
                        BitVecOp::BVV(value) => ctx.bvv(value.extract(*f as usize, *t as usize)?),

                        // Concat cases

                        // Extracting the entire left side
                        BitVecOp::Concat(lhs, rhs) if *f == 0 && *t == lhs.size() => {
                            Ok(lhs.clone())
                        }
                        // Extracting the entire right side
                        BitVecOp::Concat(lhs, rhs) if *f == lhs.size() && *t == arc.size() => {
                            Ok(rhs.clone())
                        }
                        // Extracting a part of the left side
                        BitVecOp::Concat(lhs, rhs) if *t < lhs.size() => {
                            Ok(ctx.extract(lhs, *f, *t)?)
                        }
                        // Extracting a part of the right side
                        BitVecOp::Concat(lhs, rhs) if *f >= lhs.size() => {
                            Ok(ctx.extract(rhs, *f - lhs.size(), *t - lhs.size())?)
                        }
                        // Extracting a part that spans both sides
                        BitVecOp::Concat(lhs, rhs) => {
                            // Extraction spans both left and right
                            // First extract the needed parts from each side
                            let left_part = ctx.extract(lhs, *f, lhs.size())?;
                            let right_part = ctx.extract(rhs, 0, *t - lhs.size())?;

                            // Concatenate the extracted parts
                            // Simplify the result to apply further optimizations
                            ctx.concat(&left_part, &right_part)?.simplify()
                        }
                        _ => ctx.extract(&arc, *f, *t),
                    }
                }
                BitVecOp::Concat(arc, arc1) => {
                    simplify!(arc, arc1);

                    match (arc.op(), arc1.op()) {
                        (BitVecOp::BVV(value1), BitVecOp::BVV(value2)) => {
                            // Calculate the new length as the sum of both BitVec lengths
                            let new_length = value1.len() + value2.len();

                            // Shift the first value to the left to make space, then OR with the second value
                            let concatenated_value =
                                (value1.clone() << value2.len()) | value2.clone();

                            // Return a new BitVec with the concatenated result and new length
                            ctx.bvv(BitVec::from_biguint_trunc(
                                &concatenated_value.to_biguint(),
                                new_length,
                            ))
                        }
                        _ => ctx.concat(&arc, &arc1),
                    }
                }
                BitVecOp::Reverse(arc) => {
                    simplify!(arc);

                    match arc.op() {
                        BitVecOp::BVV(value) => {
                            let reversed_bits = value.reverse();
                            ctx.bvv(reversed_bits)
                        }
                        _ => ctx.reverse(&arc),
                    }
                }
                BitVecOp::FpToIEEEBV(arc) => {
                    simplify!(arc);

                    match arc.op() {
                        FloatOp::FPV(float) => {
                            // Convert the floating-point value to its IEEE 754 bit representation
                            let ieee_bits = float.to_ieee_bits();
                            let bit_length = float.fsort().size() as usize;

                            // Create a BitVec with the IEEE 754 representation
                            ctx.bvv(
                                BitVec::from_biguint(&ieee_bits, bit_length)
                                    .expect("Failed to create BitVec from BigUint"),
                            )
                        }
                        _ => ctx.fp_to_ieeebv(&arc), // Fallback for non-concrete values
                    }
                }
                BitVecOp::FpToUBV(arc, bit_size, fprm) => {
                    simplify!(arc);

                    match arc.op() {
                        FloatOp::FPV(float) => {
                            // Convert the float to an unsigned integer representation (BigUint)
                            let unsigned_value =
                                float.to_unsigned_biguint().unwrap_or(BigUint::zero());

                            // Truncate or extend the result to fit within the specified bit size
                            let result_bitvec =
                                BitVec::from_biguint_trunc(&unsigned_value, *bit_size as usize);

                            ctx.bvv(result_bitvec)
                        }
                        _ => ctx.fp_to_ubv(&arc, *bit_size, fprm.clone()), // Fallback for non-concrete values
                    }
                }
                BitVecOp::FpToSBV(arc, bit_size, fprm) => {
                    simplify!(arc);

                    match arc.op() {
                        FloatOp::FPV(float) => {
                            // Convert the float to a signed integer representation (BigInt)
                            let signed_value = float.to_signed_bigint().unwrap_or(BigInt::zero());

                            // Convert the signed value to BigUint for BitVec construction
                            let unsigned_value =
                                signed_value.to_biguint().unwrap_or(BigUint::zero());

                            // Create a BitVec with the result, truncating or extending to fit within the specified bit size
                            let result_bitvec =
                                BitVec::from_biguint_trunc(&unsigned_value, *bit_size as usize);

                            ctx.bvv(result_bitvec)
                        }
                        _ => ctx.fp_to_sbv(&arc, *bit_size, fprm.clone()), // Fallback for non-concrete values
                    }
                }
                BitVecOp::StrLen(arc) => {
                    simplify!(arc);
                    match arc.op() {
                        StringOp::StringV(value) => {
                            let length = value.len() as u64;
                            ctx.bvv(BitVec::from_prim_with_size(length, 64))
                        }
                        // _ => Err(ClarirsError::InvalidArguments),
                        _ => ctx.strlen(&arc), // Fallback to symbolic
                    }
                }
                BitVecOp::StrIndexOf(arc, arc1, arc2) => {
                    simplify!(arc, arc1, arc2); // Simplify all arguments

                    match (arc.op(), arc1.op(), arc2.op()) {
                        (
                            StringOp::StringV(input_string),
                            StringOp::StringV(substring),
                            BitVecOp::BVV(start_index),
                        ) => {
                            let s = input_string;
                            let t = substring;
                            let i = start_index.to_usize().unwrap_or(0);

                            // Check if `t` exists in `s` starting from `i`
                            if i < s.len() {
                                match s[i..].find(t) {
                                    Some(pos) => {
                                        let result_index = (i + pos) as u64;
                                        ctx.bvv(BitVec::from_prim_with_size(result_index, 64))
                                    }
                                    None => ctx.bvv(BitVec::from_prim_with_size(-1i64 as u64, 64)), // -1 if not found
                                }
                            } else {
                                // If start index is out of bounds, return -1
                                ctx.bvv(BitVec::from_prim_with_size(-1i64 as u64, 64))
                            }
                        }
                        // _ => Err(ClarirsError::InvalidArguments), // Handle non-concrete cases
                        _ => ctx.strindexof(&arc, &arc1, &arc2), // Fallback to symbolic
                    }
                }
                BitVecOp::StrToBV(arc) => {
                    simplify!(arc);

                    match arc.op() {
                        StringOp::StringV(string) => {
                            // Attempt to parse the string as a decimal integer
                            let value = BigUint::from_str_radix(string, 10)
                                .or_else(|_| BigUint::from_str_radix(string, 16)) // Try hexadecimal if decimal fails
                                .or_else(|_| BigUint::from_str_radix(string, 2)) // Try binary if hexadecimal fails
                                .map_err(|_| ClarirsError::InvalidArguments)?; // Error if parsing fails

                            // Determine the bit length required to represent the number
                            let bit_length = value.bits() as usize;

                            // Convert the parsed value into a BitVec with the calculated bit length
                            let bitvec = BitVec::from_biguint_trunc(&value, bit_length);
                            ctx.bvv(bitvec)
                        }
                        _ => ctx.strtobv(&arc),
                    }
                }

                BitVecOp::If(arc, arc1, arc2) => todo!(),
                BitVecOp::Annotated(arc, annotation) => todo!(),
            }
        })
    }
}

#[allow(unused_variables)]
impl<'c> Simplify<'c> for FloatAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        let ctx = self.context();
        let hash = self.hash();

        ctx.simplification_cache.get_or_insert_with_float(hash, || {
            match &self.op() {
                FloatOp::FPS(name, fsort) => ctx.fps(name.clone(), fsort.clone()),
                FloatOp::FPV(float) => ctx.fpv(float.clone()),

                FloatOp::FpNeg(arc, _fprm) => {
                    simplify!(arc);
                    match arc.op() {
                        FloatOp::FPV(float) => {
                            // Reverse the sign of the float
                            let neg_float = Float::new(
                                !float.sign(),
                                float.exponent().clone(),
                                float.mantissa().clone(),
                            );
                            ctx.fpv(neg_float)
                        }
                        _ => Err(ClarirsError::InvalidArguments), // Handle non-float cases
                    }
                }
                FloatOp::FpAbs(arc, _fprm) => {
                    simplify!(arc);
                    match arc.op() {
                        FloatOp::FPV(float) => {
                            // Create an absolute value by setting the sign to `false`
                            let abs_float = Float::new(
                                false,
                                float.exponent().clone(),
                                float.mantissa().clone(),
                            );
                            ctx.fpv(abs_float)
                        }
                        _ => Err(ClarirsError::InvalidArguments), // Handle non-float cases
                    }
                }
                FloatOp::FpAdd(arc, arc1, fprm) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (FloatOp::FPV(float1), FloatOp::FPV(float2)) => {
                            ctx.fpv(float1.clone() + float2.clone())
                        }
                        _ => ctx.fp_add(&arc, &arc1, fprm.clone()),
                    }
                }
                FloatOp::FpSub(arc, arc1, fprm) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (FloatOp::FPV(float1), FloatOp::FPV(float2)) => {
                            ctx.fpv(float1.clone() - float2.clone())
                        }
                        _ => ctx.fp_sub(&arc, &arc1, fprm.clone()),
                    }
                }
                FloatOp::FpMul(arc, arc1, fprm) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (FloatOp::FPV(float1), FloatOp::FPV(float2)) => {
                            ctx.fpv(float1.clone() * float2.clone())
                        }
                        _ => ctx.fp_mul(&arc, &arc1, fprm.clone()),
                    }
                }
                FloatOp::FpDiv(arc, arc1, fprm) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (FloatOp::FPV(float1), FloatOp::FPV(float2)) => {
                            ctx.fpv(float1.clone() / float2.clone())
                        }
                        _ => ctx.fp_div(&arc, &arc1, fprm.clone()),
                    }
                }
                FloatOp::FpSqrt(arc, fprm) => {
                    simplify!(arc);
                    match arc.op() {
                        FloatOp::FPV(float_val) => {
                            // Calculate the square root, handling potential `None` from `to_f64()`
                            if let Some(float_as_f64) = float_val.to_f64() {
                                let sqrt_value = float_as_f64.sqrt();
                                ctx.fpv(Float::from_f64_with_rounding(
                                    sqrt_value,
                                    fprm.clone(),
                                    float_val.fsort(),
                                ))
                            } else {
                                Err(ClarirsError::InvalidArguments)
                            }
                        }
                        _ => ctx.fp_sqrt(&arc, fprm.clone()),
                    }
                }
                FloatOp::FpToFp(arc, fsort, fprm) => {
                    simplify!(arc);
                    match arc.op() {
                        FloatOp::FPV(float_val) => {
                            let converted_value =
                                float_val.convert_to_format(fsort.clone(), fprm.clone());
                            ctx.fpv(converted_value)
                        }
                        _ => ctx.fp_to_fp(&arc, fsort.clone(), fprm.clone()),
                    }
                }
                FloatOp::BvToFpUnsigned(arc, fsort, fprm) => {
                    simplify!(arc);
                    match arc.op() {
                        BitVecOp::BVV(bv_val) => {
                            // Interpret `bv_val` as an unsigned integer and convert to float
                            let float_value = Float::from_unsigned_biguint_with_rounding(
                                &bv_val.to_biguint(),
                                fsort.clone(),
                                fprm.clone(),
                            );
                            ctx.fpv(float_value)
                        }
                        _ => ctx.bv_to_fp_unsigned(&arc, fsort.clone(), fprm.clone()),
                    }
                }
                FloatOp::If(arc, arc1, arc2) => todo!(),
                FloatOp::Annotated(arc, annotation) => todo!(),
            }
        })
    }
}

#[allow(unused_variables)]
impl<'c> Simplify<'c> for StringAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        let ctx = self.context();
        let hash = self.hash();

        ctx.simplification_cache
            .get_or_insert_with_string(hash, || {
                match &self.op() {
                    StringOp::StringS(name) => ctx.strings(name.clone()),
                    StringOp::StringV(value) => ctx.stringv(value.clone()),
                    StringOp::StrConcat(arc, arc1) => {
                        simplify!(arc, arc1);
                        match (arc.op(), arc1.op()) {
                            (StringOp::StringV(str1), StringOp::StringV(str2)) => {
                                let concatenated = format!("{}{}", str1, str2);
                                ctx.stringv(concatenated)
                            }
                            _ => ctx.strconcat(&arc, &arc1),
                        }
                    }
                    StringOp::StrSubstr(arc, arc1, arc2) => {
                        simplify!(arc, arc1, arc2);
                        match (arc.op(), arc1.op(), arc2.op()) {
                            (
                                StringOp::StringV(str),
                                BitVecOp::BVV(start),
                                BitVecOp::BVV(length),
                            ) => {
                                // Convert start and length to isize, then handle them as usize if they are non-negative
                                let start = start.to_usize().unwrap_or(0).max(0);
                                let length = length.to_usize().unwrap_or(str.len()).max(0);
                                let end = start.saturating_add(length).min(str.len());

                                // Extract the substring safely within bounds
                                let substring = str.get(start..end).unwrap_or("").to_string();
                                ctx.stringv(substring)
                            }
                            _ => ctx.strsubstr(&arc, &arc1, &arc2),
                        }
                    }
                    StringOp::StrReplace(arc, arc1, arc2) => {
                        simplify!(arc, arc1, arc2); // Simplify all arguments
                        match (arc.op(), arc1.op(), arc2.op()) {
                            (
                                StringOp::StringV(initial),
                                StringOp::StringV(pattern),
                                StringOp::StringV(replacement),
                            ) => {
                                // Case: Replace first occurrence of `pattern` with `replacement` in `initial` as per ClariPy DONE
                                let new_value = initial.replacen(pattern, replacement, 1);
                                // Case: Replace all occurrences of `pattern` with `replacement` in `initial` LEFT
                                // let new_value = initial.replace(pattern, replacement);
                                ctx.stringv(new_value)
                            }
                            _ => ctx.strreplace(&arc, &arc1, &arc2), // Fallback to symbolic StrReplace
                        }
                    }
                    StringOp::BVToStr(arc) => {
                        simplify!(arc);

                        match arc.op() {
                            BitVecOp::BVV(value) => {
                                // Convert the BitVec value to an integer, then to a string
                                let int_value = value.to_biguint();
                                let string_value = int_value.to_string();

                                ctx.stringv(string_value)
                            }
                            _ => ctx.bvtostr(&arc),
                        }
                    }
                    StringOp::If(arc, arc1, arc2) => todo!(),
                    StringOp::Annotated(arc, annotation) => todo!(),
                }
            })
    }
}
