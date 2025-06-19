use crate::algorithms::post_order::walk_post_order;
use crate::prelude::*;

/// Trait for removing all annotations from an AST
pub trait Deannotate<'c>: Sized {
    /// Remove all annotations from this AST, returning a new AST without annotations
    fn deannotate(&self) -> Result<Self, ClarirsError>;
}

impl<'c> Deannotate<'c> for BoolAst<'c> {
    fn deannotate(&self) -> Result<Self, ClarirsError> {
        DynAst::from(self).deannotate()?.try_into().map_err(|_| {
            ClarirsError::TypeError("Failed to convert DynAst back to BoolAst".to_string())
        })
    }
}

impl<'c> Deannotate<'c> for BitVecAst<'c> {
    fn deannotate(&self) -> Result<Self, ClarirsError> {
        DynAst::from(self).deannotate()?.try_into().map_err(|_| {
            ClarirsError::TypeError("Failed to convert DynAst back to BitVecAst".to_string())
        })
    }
}

impl<'c> Deannotate<'c> for FloatAst<'c> {
    fn deannotate(&self) -> Result<Self, ClarirsError> {
        DynAst::from(self).deannotate()?.try_into().map_err(|_| {
            ClarirsError::TypeError("Failed to convert DynAst back to FloatAst".to_string())
        })
    }
}

impl<'c> Deannotate<'c> for StringAst<'c> {
    fn deannotate(&self) -> Result<Self, ClarirsError> {
        DynAst::from(self).deannotate()?.try_into().map_err(|_| {
            ClarirsError::TypeError("Failed to convert DynAst back to StringAst".to_string())
        })
    }
}

impl<'c> Deannotate<'c> for DynAst<'c> {
    fn deannotate(&self) -> Result<Self, ClarirsError> {
        let ctx = self.context();
        walk_post_order::<DynAst>(
            self.clone(),
            |ast, children| {
                match &ast {
                    DynAst::Boolean(bool_ast) => {
                        match bool_ast.op() {
                            BooleanOp::BoolS(_) | BooleanOp::BoolV(_) => Ok(bool_ast.clone()),
                            BooleanOp::Not(..) => ctx.not(&children[0].clone().try_into()?),
                            BooleanOp::And(..) => ctx.and(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::Or(..) => ctx.or(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::Xor(..) => ctx.xor(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::BoolEq(..) => ctx.eq_::<BooleanOp>(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::BoolNeq(..) => ctx.neq::<BooleanOp>(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::Eq(..) => ctx.eq_::<BitVecOp>(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::Neq(..) => ctx.neq::<BitVecOp>(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::ULT(..) => ctx.ult(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::ULE(..) => ctx.ule(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::UGT(..) => ctx.ugt(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::UGE(..) => ctx.uge(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::SLT(..) => ctx.slt(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::SLE(..) => ctx.sle(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::SGT(..) => ctx.sgt(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::SGE(..) => ctx.sge(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::FpEq(..) => ctx.fp_eq(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::FpNeq(..) => ctx.fp_neq(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::FpLt(..) => ctx.fp_lt(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::FpLeq(..) => ctx.fp_leq(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::FpGt(..) => ctx.fp_gt(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::FpGeq(..) => ctx.fp_geq(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::FpIsNan(..) => {
                                ctx.fp_is_nan(&children[0].clone().try_into()?)
                            }
                            BooleanOp::FpIsInf(..) => {
                                ctx.fp_is_inf(&children[0].clone().try_into()?)
                            }
                            BooleanOp::StrContains(..) => ctx.strcontains(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::StrPrefixOf(..) => ctx.strprefixof(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::StrSuffixOf(..) => ctx.strsuffixof(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::StrIsDigit(..) => {
                                ctx.strisdigit(&children[0].clone().try_into()?)
                            }
                            BooleanOp::StrEq(..) => ctx.streq(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::StrNeq(..) => ctx.strneq(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BooleanOp::If(..) => ctx.if_(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                                &children[2].clone().try_into()?,
                            ),
                            BooleanOp::Annotated(..) => {
                                // For annotated nodes, return the child (removing the annotation)
                                children[0].clone().try_into()
                            }
                        }
                        .map(DynAst::from)
                    }
                    DynAst::BitVec(bv_ast) => {
                        match bv_ast.op() {
                            BitVecOp::BVS(..) | BitVecOp::BVV(..) | BitVecOp::SI(..) => {
                                Ok(bv_ast.clone())
                            }
                            BitVecOp::Not(..) => ctx.not(&children[0].clone().try_into()?),
                            BitVecOp::And(..) => ctx.and(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::Or(..) => ctx.or(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::Xor(..) => ctx.xor(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::Neg(..) => ctx.neg(&children[0].clone().try_into()?),
                            BitVecOp::Add(..) => ctx.add(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::Sub(..) => ctx.sub(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::Mul(..) => ctx.mul(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::UDiv(..) => ctx.udiv(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::SDiv(..) => ctx.sdiv(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::URem(..) => ctx.urem(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::SRem(..) => ctx.srem(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::ShL(..) => ctx.shl(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::LShR(..) => ctx.lshr(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::AShR(..) => ctx.ashr(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::RotateLeft(..) => ctx.rotate_left(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::RotateRight(..) => ctx.rotate_right(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::ZeroExt(_, amount) => {
                                ctx.zero_ext(&children[0].clone().try_into()?, *amount)
                            }
                            BitVecOp::SignExt(_, amount) => {
                                ctx.sign_ext(&children[0].clone().try_into()?, *amount)
                            }
                            BitVecOp::Extract(_, high, low) => {
                                ctx.extract(&children[0].clone().try_into()?, *high, *low)
                            }
                            BitVecOp::Concat(..) => ctx.concat(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::Reverse(..) => ctx.reverse(&children[0].clone().try_into()?),
                            BitVecOp::FpToIEEEBV(..) => {
                                ctx.fp_to_ieeebv(&children[0].clone().try_into()?)
                            }
                            BitVecOp::FpToUBV(_, size, rm) => {
                                ctx.fp_to_ubv(&children[0].clone().try_into()?, *size, *rm)
                            }
                            BitVecOp::FpToSBV(_, size, rm) => {
                                ctx.fp_to_sbv(&children[0].clone().try_into()?, *size, *rm)
                            }
                            BitVecOp::StrLen(..) => ctx.strlen(&children[0].clone().try_into()?),
                            BitVecOp::StrIndexOf(..) => ctx.strindexof(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                                &children[2].clone().try_into()?,
                            ),
                            BitVecOp::StrToBV(..) => ctx.strtobv(&children[0].clone().try_into()?),
                            BitVecOp::If(..) => ctx.if_(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                                &children[2].clone().try_into()?,
                            ),
                            BitVecOp::Annotated(..) => {
                                // For annotated nodes, return the child (removing the annotation)
                                children[0].clone().try_into()
                            }
                            BitVecOp::Union(..) => ctx.union(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                            BitVecOp::Intersection(..) => ctx.intersection(
                                &children[0].clone().try_into()?,
                                &children[1].clone().try_into()?,
                            ),
                        }
                        .map(DynAst::from)
                    }
                    DynAst::Float(float_ast) => match float_ast.op() {
                        FloatOp::FPS(..) | FloatOp::FPV(..) => Ok(float_ast.clone()),
                        FloatOp::FpNeg(..) => ctx.fp_neg(&children[0].clone().try_into()?),
                        FloatOp::FpAbs(..) => ctx.fp_abs(&children[0].clone().try_into()?),
                        FloatOp::FpAdd(_, _, rm) => ctx.fp_add(
                            &children[0].clone().try_into()?,
                            &children[1].clone().try_into()?,
                            *rm,
                        ),
                        FloatOp::FpSub(_, _, rm) => ctx.fp_sub(
                            &children[0].clone().try_into()?,
                            &children[1].clone().try_into()?,
                            *rm,
                        ),
                        FloatOp::FpMul(_, _, rm) => ctx.fp_mul(
                            &children[0].clone().try_into()?,
                            &children[1].clone().try_into()?,
                            *rm,
                        ),
                        FloatOp::FpDiv(_, _, rm) => ctx.fp_div(
                            &children[0].clone().try_into()?,
                            &children[1].clone().try_into()?,
                            *rm,
                        ),
                        FloatOp::FpSqrt(_, rm) => {
                            ctx.fp_sqrt(&children[0].clone().try_into()?, *rm)
                        }
                        FloatOp::FpToFp(_, sort, rm) => {
                            ctx.fp_to_fp(&children[0].clone().try_into()?, *sort, *rm)
                        }
                        FloatOp::BvToFp(_, rm) => {
                            ctx.bv_to_fp(&children[0].clone().try_into()?, *rm)
                        }
                        FloatOp::BvToFpSigned(_, sort, rm) => {
                            ctx.bv_to_fp_signed(&children[0].clone().try_into()?, *sort, *rm)
                        }
                        FloatOp::BvToFpUnsigned(_, sort, rm) => {
                            ctx.bv_to_fp_unsigned(&children[0].clone().try_into()?, *sort, *rm)
                        }
                        FloatOp::If(..) => ctx.if_(
                            &children[0].clone().try_into()?,
                            &children[1].clone().try_into()?,
                            &children[2].clone().try_into()?,
                        ),
                        FloatOp::Annotated(..) => {
                            // For annotated nodes, return the child (removing the annotation)
                            children[0].clone().try_into()
                        }
                    }
                    .map(DynAst::from),
                    DynAst::String(string_ast) => match string_ast.op() {
                        StringOp::StringS(_) | StringOp::StringV(_) => Ok(string_ast.clone()),
                        StringOp::StrConcat(..) => ctx.strconcat(
                            &children[0].clone().try_into()?,
                            &children[1].clone().try_into()?,
                        ),
                        StringOp::StrSubstr(..) => ctx.strsubstr(
                            &children[0].clone().try_into()?,
                            &children[1].clone().try_into()?,
                            &children[2].clone().try_into()?,
                        ),
                        StringOp::StrReplace(..) => ctx.strreplace(
                            &children[0].clone().try_into()?,
                            &children[1].clone().try_into()?,
                            &children[2].clone().try_into()?,
                        ),
                        StringOp::BVToStr(..) => ctx.bvtostr(&children[0].clone().try_into()?),
                        StringOp::If(..) => ctx.if_(
                            &children[0].clone().try_into()?,
                            &children[1].clone().try_into()?,
                            &children[2].clone().try_into()?,
                        ),
                        StringOp::Annotated(..) => {
                            // For annotated nodes, return the child (removing the annotation)
                            children[0].clone().try_into()
                        }
                    }
                    .map(DynAst::from),
                }
            },
            &(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deannotate_bool() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bools("x")?;
        let y = ctx.bools("y")?;
        let eq = ctx.eq_(&x, &y)?;

        // Add an annotation
        let annotated = ctx.make_bool(BooleanOp::Annotated(
            eq,
            Annotation::new(
                AnnotationType::Unknown {
                    name: "test".to_string(),
                    value: vec![],
                },
                true,
                true,
            ),
        ))?;

        // Deannotate should remove the annotation
        let deannotated = annotated.deannotate()?;

        // The result should be equivalent to the original but without annotation
        match deannotated.op() {
            BooleanOp::BoolEq(_, _) => {} // Success - annotation was removed
            _ => panic!("Expected BoolEq operation, got {:?}", deannotated.op()),
        }

        Ok(())
    }

    #[test]
    fn test_deannotate_bitvec() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32)?;
        let y = ctx.bvs("y", 32)?;
        let add = ctx.add(&x, &y)?;

        // Add an annotation
        let annotated = ctx.make_bitvec(BitVecOp::Annotated(
            add,
            Annotation::new(
                AnnotationType::Unknown {
                    name: "test".to_string(),
                    value: vec![],
                },
                true,
                true,
            ),
        ))?;

        // Deannotate should remove the annotation
        let deannotated = annotated.deannotate()?;

        // The result should be equivalent to the original but without annotation
        match deannotated.op() {
            BitVecOp::Add(_, _) => {} // Success - annotation was removed
            _ => panic!("Expected Add operation, got {:?}", deannotated.op()),
        }

        Ok(())
    }

    #[test]
    fn test_deannotate_nested() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32)?;
        let y = ctx.bvs("y", 32)?;

        // Create nested annotations
        let annotated_x = ctx.make_bitvec(BitVecOp::Annotated(
            x,
            Annotation::new(
                AnnotationType::Unknown {
                    name: "x_anno".to_string(),
                    value: vec![],
                },
                true,
                true,
            ),
        ))?;
        let annotated_y = ctx.make_bitvec(BitVecOp::Annotated(
            y,
            Annotation::new(
                AnnotationType::Unknown {
                    name: "y_anno".to_string(),
                    value: vec![],
                },
                true,
                true,
            ),
        ))?;
        let add = ctx.add(&annotated_x, &annotated_y)?;
        let annotated_add = ctx.make_bitvec(BitVecOp::Annotated(
            add,
            Annotation::new(
                AnnotationType::Unknown {
                    name: "add_anno".to_string(),
                    value: vec![],
                },
                true,
                true,
            ),
        ))?;

        // Deannotate should remove all annotations
        let deannotated = annotated_add.deannotate()?;

        // Verify the structure is correct and all annotations are removed
        match deannotated.op() {
            BitVecOp::Add(a, b) => {
                match (a.op(), b.op()) {
                    (BitVecOp::BVS(..), BitVecOp::BVS(..)) => {} // Success - all annotations removed
                    _ => panic!("Expected BVS operations for operands"),
                }
            }
            _ => panic!("Expected Add operation, got {:?}", deannotated.op()),
        }

        Ok(())
    }
}
