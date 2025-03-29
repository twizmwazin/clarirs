use crate::{
    algorithms::simplify::{extract_bitvec_child, extract_bool_child, extract_float_child},
    prelude::*,
};

pub(crate) fn simplify_float<'c>(
    ast: &FloatAst<'c>,
    children: &Vec<DynAst<'c>>,
) -> Result<FloatAst<'c>, ClarirsError> {
    let ctx = ast.context();

    match &ast.op() {
        FloatOp::FPS(name, fsort) => ctx.fps(name.clone(), fsort.clone()),
        FloatOp::FPV(float) => ctx.fpv(float.clone()),

        FloatOp::FpNeg(..) => {
            let arc = extract_float_child!(children, 0);
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
                _ => ctx.fp_neg(&arc), // Handle non-concrete cases
            }
        }
        FloatOp::FpAbs(..) => {
            let arc = extract_float_child!(children, 0);
            match arc.op() {
                FloatOp::FPV(float) => {
                    // Create an absolute value by setting the sign to `false`
                    let abs_float =
                        Float::new(false, float.exponent().clone(), float.mantissa().clone());
                    ctx.fpv(abs_float)
                }
                _ => ctx.fp_abs(&arc), // Handle non-concrete cases
            }
        }
        FloatOp::FpAdd(_, _, fprm) => {
            let (arc, arc1) = (
                extract_float_child!(children, 0),
                extract_float_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(float1), FloatOp::FPV(float2)) => {
                    ctx.fpv((float1.clone() + float2.clone())?)
                }
                _ => ctx.fp_add(&arc, &arc1, fprm.clone()),
            }
        }
        FloatOp::FpSub(_, _, fprm) => {
            let (arc, arc1) = (
                extract_float_child!(children, 0),
                extract_float_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(float1), FloatOp::FPV(float2)) => {
                    ctx.fpv((float1.clone() - float2.clone())?)
                }
                _ => ctx.fp_sub(&arc, &arc1, fprm.clone()),
            }
        }
        FloatOp::FpMul(_, _, fprm) => {
            let (arc, arc1) = (
                extract_float_child!(children, 0),
                extract_float_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(float1), FloatOp::FPV(float2)) => {
                    ctx.fpv((float1.clone() * float2.clone())?)
                }
                _ => ctx.fp_mul(&arc, &arc1, fprm.clone()),
            }
        }
        FloatOp::FpDiv(_, _, fprm) => {
            let (arc, arc1) = (
                extract_float_child!(children, 0),
                extract_float_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (FloatOp::FPV(float1), FloatOp::FPV(float2)) => {
                    ctx.fpv((float1.clone() / float2.clone())?)
                }
                _ => ctx.fp_div(&arc, &arc1, fprm.clone()),
            }
        }
        FloatOp::FpSqrt(_, fprm) => {
            let arc = extract_float_child!(children, 0);
            match arc.op() {
                FloatOp::FPV(float_val) => {
                    // Calculate the square root, handling potential `None` from `to_f64()`
                    if let Some(float_as_f64) = float_val.to_f64() {
                        let sqrt_value = float_as_f64.sqrt();
                        ctx.fpv(Float::from_f64_with_rounding(
                            sqrt_value,
                            fprm.clone(),
                            float_val.fsort(),
                        )?)
                    } else {
                        Err(ClarirsError::InvalidArguments)
                    }
                }
                _ => ctx.fp_sqrt(&arc, fprm.clone()),
            }
        }
        FloatOp::FpToFp(_, fsort, fprm) => {
            let arc = extract_float_child!(children, 0);
            match arc.op() {
                FloatOp::FPV(float_val) => {
                    let converted_value = float_val.convert_to_format(fsort.clone(), fprm.clone());
                    ctx.fpv(converted_value?)
                }
                _ => ctx.fp_to_fp(&arc, fsort.clone(), fprm.clone()),
            }
        }
        FloatOp::BvToFp(_, fsort) => {
            let arc = extract_bitvec_child!(children, 0);
            ctx.bv_to_fp(&arc, fsort.clone())
        }
        FloatOp::BvToFpSigned(_, fsort, fprm) => {
            let arc = extract_bitvec_child!(children, 0);
            match arc.op() {
                BitVecOp::BVV(bv_val) => {
                    // Handle conversion from signed bitvector to float
                    let float_value = Float::from_bigint_with_rounding(
                        &bv_val.to_bigint(),
                        fsort.clone(),
                        fprm.clone(),
                    )?;
                    ctx.fpv(float_value)
                }
                _ => ctx.bv_to_fp_signed(&arc, fsort.clone(), fprm.clone()),
            }
        }
        FloatOp::BvToFpUnsigned(_, fsort, fprm) => {
            let arc = extract_bitvec_child!(children, 0);
            match arc.op() {
                BitVecOp::BVV(bv_val) => {
                    // Interpret `bv_val` as an unsigned integer and convert to float
                    let float_value = Float::from_biguint_with_rounding(
                        &bv_val.to_biguint(),
                        fsort.clone(),
                        fprm.clone(),
                    );
                    ctx.fpv(float_value?)
                }
                _ => ctx.bv_to_fp_unsigned(&arc, fsort.clone(), fprm.clone()),
            }
        }
        FloatOp::If(..) => {
            let (if_, then_, else_) = (
                extract_bool_child!(children, 0),
                extract_float_child!(children, 1),
                extract_float_child!(children, 2),
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
        FloatOp::Annotated(_, annotation) => {
            let arc = extract_float_child!(children, 0);
            if annotation.eliminatable() {
                Ok(arc)
            } else if annotation.relocatable() {
                ctx.annotated(&arc, annotation.clone())
            } else {
                Ok(ast.clone())
            }
        }
    }
}
