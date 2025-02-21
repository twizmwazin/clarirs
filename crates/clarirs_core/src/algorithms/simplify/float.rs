use crate::{algorithms::simplify::simplify, prelude::*};

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
                            ctx.fpv((float1.clone() + float2.clone())?)
                        }
                        _ => ctx.fp_add(&arc, &arc1, fprm.clone()),
                    }
                }
                FloatOp::FpSub(arc, arc1, fprm) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (FloatOp::FPV(float1), FloatOp::FPV(float2)) => {
                            ctx.fpv((float1.clone() - float2.clone())?)
                        }
                        _ => ctx.fp_sub(&arc, &arc1, fprm.clone()),
                    }
                }
                FloatOp::FpMul(arc, arc1, fprm) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (FloatOp::FPV(float1), FloatOp::FPV(float2)) => {
                            ctx.fpv((float1.clone() * float2.clone())?)
                        }
                        _ => ctx.fp_mul(&arc, &arc1, fprm.clone()),
                    }
                }
                FloatOp::FpDiv(arc, arc1, fprm) => {
                    simplify!(arc, arc1);
                    match (arc.op(), arc1.op()) {
                        (FloatOp::FPV(float1), FloatOp::FPV(float2)) => {
                            ctx.fpv((float1.clone() / float2.clone())?)
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
                                )?)
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
                            ctx.fpv(converted_value?)
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
                            ctx.fpv(float_value?)
                        }
                        _ => ctx.bv_to_fp_unsigned(&arc, fsort.clone(), fprm.clone()),
                    }
                }
                FloatOp::If(arc, arc1, arc2) => todo!("fp if simplification"),
                FloatOp::Annotated(arc, annotation) => todo!("fp annotation simplification"),
            }
        })
    }
}
