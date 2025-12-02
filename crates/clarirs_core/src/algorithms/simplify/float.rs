use crate::prelude::*;

pub(crate) fn simplify_float<'c>(
    state: &mut super::SimplifyState<'c>,
) -> Result<FloatAst<'c>, ClarirsError> {
    let ctx = state.expr.context();
    let float_expr = state.expr.clone().into_float().unwrap();

    match &float_expr.op() {
        FloatOp::FPS(..) | FloatOp::FPV(_) => Ok(float_expr),

        FloatOp::FpFP(..) => {
            let sign = state.get_bv_child(0)?;
            let exp = state.get_bv_child(1)?;
            let sig = state.get_bv_child(2)?;

            // If all components are concrete, construct a concrete float
            match (sign.op(), exp.op(), sig.op()) {
                (BitVecOp::BVV(sign_bv), BitVecOp::BVV(exp_bv), BitVecOp::BVV(sig_bv)) => {
                    let float = Float::new(
                        !sign_bv.is_zero(), // sign is true if bit is 1
                        exp_bv.clone(),
                        sig_bv.clone(),
                    );
                    ctx.fpv(float?)
                }
                _ => ctx.fp_fp(&sign, &exp, &sig),
            }
        }

        FloatOp::FpNeg(..) => {
            let arc = state.get_fp_child(0)?;
            match arc.op() {
                FloatOp::FPV(float) => ctx.fpv(-*float),
                _ => ctx.fp_neg(&arc),
            }
        }
        FloatOp::FpAbs(..) => {
            let arc = state.get_fp_child(0)?;
            match arc.op() {
                FloatOp::FPV(float) => ctx.fpv(float.abs()),
                _ => ctx.fp_abs(&arc),
            }
        }
        FloatOp::FpAdd(_, _, fprm) => {
            let (arc, arc1) = (state.get_fp_child(0)?, state.get_fp_child(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(float1), FloatOp::FPV(float2)) => ctx.fpv(*float1 + *float2),
                _ => ctx.fp_add(&arc, &arc1, *fprm),
            }
        }
        FloatOp::FpSub(_, _, fprm) => {
            let (arc, arc1) = (state.get_fp_child(0)?, state.get_fp_child(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(float1), FloatOp::FPV(float2)) => ctx.fpv(*float1 - *float2),
                _ => ctx.fp_sub(&arc, &arc1, *fprm),
            }
        }
        FloatOp::FpMul(_, _, fprm) => {
            let (arc, arc1) = (state.get_fp_child(0)?, state.get_fp_child(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(float1), FloatOp::FPV(float2)) => ctx.fpv(*float1 * *float2),
                _ => ctx.fp_mul(&arc, &arc1, *fprm),
            }
        }
        FloatOp::FpDiv(_, _, fprm) => {
            let (arc, arc1) = (state.get_fp_child(0)?, state.get_fp_child(1)?);
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(float1), FloatOp::FPV(float2)) => ctx.fpv(*float1 / *float2),
                _ => ctx.fp_div(&arc, &arc1, *fprm),
            }
        }
        FloatOp::FpSqrt(_, fprm) => {
            let arc = state.get_fp_child(0)?;
            match arc.op() {
                FloatOp::FPV(float_val) => ctx.fpv(float_val.sqrt()),
                _ => ctx.fp_sqrt(&arc, *fprm),
            }
        }
        FloatOp::FpToFp(_, fsort, fprm) => {
            let arc = state.get_fp_child(0)?;
            match arc.op() {
                FloatOp::FPV(float_val) if float_val.fsort() == *fsort => Ok(arc),
                FloatOp::FPV(float_val) => {
                    let converted_value = float_val.convert_to_format(*fsort, *fprm);
                    ctx.fpv(converted_value?)
                }
                _ => ctx.fp_to_fp(&arc, *fsort, *fprm),
            }
        }
        FloatOp::BvToFp(_, fsort) => {
            let arc = state.get_bv_child(0)?;
            match arc.op() {
                BitVecOp::BVV(bv_val) => {
                    // Extract sign, exponent, and mantissa from IEEE 754 representation
                    let total_bits = bv_val.len();
                    let man_bits = fsort.mantissa;

                    // Ensure the bitvector size matches the float sort
                    if total_bits != fsort.size() {
                        return Err(ClarirsError::InvalidArguments);
                    }

                    // Extract components: sign (1 bit) | exponent (exp_bits) | mantissa (man_bits)
                    let sign_bit = bv_val.extract(total_bits - 1, total_bits - 1)?;
                    let exponent = bv_val.extract(man_bits, total_bits - 2)?;
                    let mantissa = bv_val.extract(0, man_bits - 1)?;

                    // Construct Float from components
                    let float = Float::new(
                        !sign_bit.is_zero(), // sign is true if bit is 1
                        exponent,
                        mantissa,
                    );
                    ctx.fpv(float?)
                }
                _ => ctx.bv_to_fp(&arc, *fsort),
            }
        }
        FloatOp::BvToFpSigned(_, fsort, fprm) => {
            let arc = state.get_bv_child(0)?;
            match arc.op() {
                BitVecOp::BVV(bv_val) => {
                    // Handle conversion from signed bitvector to float
                    let float_value =
                        Float::from_bigint_with_rounding(&bv_val.to_bigint(), *fsort, *fprm)?;
                    ctx.fpv(float_value)
                }
                _ => ctx.bv_to_fp_signed(&arc, *fsort, *fprm),
            }
        }
        FloatOp::BvToFpUnsigned(_, fsort, fprm) => {
            let arc = state.get_bv_child(0)?;
            match arc.op() {
                BitVecOp::BVV(bv_val) => {
                    // Interpret `bv_val` as an unsigned integer and convert to float
                    let float_value =
                        Float::from_biguint_with_rounding(&bv_val.to_biguint(), *fsort, *fprm);
                    ctx.fpv(float_value?)
                }
                _ => ctx.bv_to_fp_unsigned(&arc, *fsort, *fprm),
            }
        }
        FloatOp::If(..) => {
            let (if_, then_, else_) = (
                state.get_bool_child(0)?,
                state.get_fp_child(1)?,
                state.get_fp_child(2)?,
            );

            // If both branches are identical, return either one
            if then_ == else_ {
                return Ok(then_.clone());
            }

            match if_.op() {
                // If the condition is a concrete boolean value, return the appropriate branch
                BooleanOp::BoolV(value) => {
                    if *value {
                        Ok(then_.clone())
                    } else {
                        Ok(else_.clone())
                    }
                }
                // If the condition has a Not at the top level, invert the branches
                BooleanOp::Not(inner) => ctx.if_(inner, &else_, &then_),
                _ => ctx.if_(&if_, &then_, &else_),
            }
        }
    }
}
