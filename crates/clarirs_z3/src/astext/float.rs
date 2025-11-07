use clarirs_core::prelude::*;
use clarirs_z3_sys as z3;

use super::AstExtZ3;
use crate::{Z3_CONTEXT, rc::RcAst};

fn fprm_to_z3(rm: FPRM) -> z3::Ast {
    Z3_CONTEXT.with(|&z3_ctx| unsafe {
        match rm {
            FPRM::NearestTiesToEven => z3::mk_fpa_rne(z3_ctx),
            FPRM::TowardPositive => z3::mk_fpa_rtp(z3_ctx),
            FPRM::TowardNegative => z3::mk_fpa_rtn(z3_ctx),
            FPRM::TowardZero => z3::mk_fpa_rtz(z3_ctx),
            FPRM::NearestTiesToAway => z3::mk_fpa_rna(z3_ctx),
        }
    })
}

fn fsort_to_z3(sort: FSort) -> z3::Sort {
    Z3_CONTEXT.with(|&z3_ctx| unsafe { z3::mk_fpa_sort(z3_ctx, sort.exponent, sort.mantissa + 1) })
}

pub(crate) fn to_z3(ast: &FloatAst, children: &[RcAst]) -> Result<RcAst, ClarirsError> {
    Z3_CONTEXT.with(|&z3_ctx| unsafe {
        Ok(match ast.op() {
            FloatOp::FPS(s, sort) => {
                let s_cstr = std::ffi::CString::new(s.as_str()).unwrap();
                let sym = z3::mk_string_symbol(z3_ctx, s_cstr.as_ptr());
                let z3_sort = fsort_to_z3(*sort);
                RcAst::from(z3::mk_const(z3_ctx, sym, z3_sort))
            }
            FloatOp::FPV(f) => {
                let sort = fsort_to_z3(f.fsort());
                match f {
                    Float::F32(val) => z3::mk_fpa_numeral_float(z3_ctx, *val, sort).into(),
                    Float::F64(val) => z3::mk_fpa_numeral_double(z3_ctx, *val, sort).into(),
                }
            }
            FloatOp::FpNeg(..) => unop!(z3_ctx, children, mk_fpa_neg),
            FloatOp::FpAbs(..) => unop!(z3_ctx, children, mk_fpa_abs),
            FloatOp::FpAdd(_, _, rm) => {
                let rm_ast = fprm_to_z3(*rm);
                let a = child!(children, 0);
                let b = child!(children, 1);
                z3::mk_fpa_add(z3_ctx, rm_ast, a.0, b.0).into()
            }
            FloatOp::FpSub(_, _, rm) => {
                let rm_ast = fprm_to_z3(*rm);
                let a = child!(children, 0);
                let b = child!(children, 1);
                z3::mk_fpa_sub(z3_ctx, rm_ast, a.0, b.0).into()
            }
            FloatOp::FpMul(_, _, rm) => {
                let rm_ast = fprm_to_z3(*rm);
                let a = child!(children, 0);
                let b = child!(children, 1);
                z3::mk_fpa_mul(z3_ctx, rm_ast, a.0, b.0).into()
            }
            FloatOp::FpDiv(_, _, rm) => {
                let rm_ast = fprm_to_z3(*rm);
                let a = child!(children, 0);
                let b = child!(children, 1);
                z3::mk_fpa_div(z3_ctx, rm_ast, a.0, b.0).into()
            }
            FloatOp::FpSqrt(_, rm) => {
                let rm_ast = fprm_to_z3(*rm);
                let a = child!(children, 0);
                z3::mk_fpa_sqrt(z3_ctx, rm_ast, a.0).into()
            }
            FloatOp::FpToFp(_, sort, rm) => {
                let rm_ast = fprm_to_z3(*rm);
                let a = child!(children, 0);
                let z3_sort = fsort_to_z3(*sort);
                z3::mk_fpa_to_fp_float(z3_ctx, rm_ast, a.0, z3_sort).into()
            }
            FloatOp::FpFP(..) => {
                let sign = child!(children, 0);
                let exp = child!(children, 1);
                let sig = child!(children, 2);
                z3::mk_fpa_fp(z3_ctx, sign.0, exp.0, sig.0).into()
            }
            FloatOp::BvToFp(_, sort) => {
                let a = child!(children, 0);
                let z3_sort = fsort_to_z3(*sort);
                z3::mk_fpa_to_fp_bv(z3_ctx, a.0, z3_sort).into()
            }
            FloatOp::BvToFpSigned(_, sort, rm) => {
                let rm_ast = fprm_to_z3(*rm);
                let a = child!(children, 0);
                let z3_sort = fsort_to_z3(*sort);
                z3::mk_fpa_to_fp_signed(z3_ctx, rm_ast, a.0, z3_sort).into()
            }
            FloatOp::BvToFpUnsigned(_, sort, rm) => {
                let rm_ast = fprm_to_z3(*rm);
                let a = child!(children, 0);
                let z3_sort = fsort_to_z3(*sort);
                z3::mk_fpa_to_fp_unsigned(z3_ctx, rm_ast, a.0, z3_sort).into()
            }
            FloatOp::If(..) => {
                let cond = child!(children, 0);
                let then = child!(children, 1);
                let else_ = child!(children, 2);
                z3::mk_ite(z3_ctx, cond.0, then.0, else_.0).into()
            }
        })
        .and_then(|ast| {
            if ast.is_null() {
                Err(ClarirsError::ConversionError(
                    "failed to create Z3 AST, got null".to_string(),
                ))
            } else {
                Ok(ast)
            }
        })
    })
}

pub(crate) fn from_z3<'c>(
    ctx: &'c Context<'c>,
    ast: impl Into<RcAst>,
) -> Result<FloatAst<'c>, ClarirsError> {
    Z3_CONTEXT.with(|z3_ctx| unsafe {
        let ast = ast.into();
        let ast_kind = z3::get_ast_kind(*z3_ctx, *ast);
        match ast_kind {
            z3::AstKind::Numeral => {
                // Get the sort to determine if it's f32 or f64
                let sort = z3::get_sort(*z3_ctx, *ast);
                let ebits = z3::fpa_get_ebits(*z3_ctx, sort);
                let sbits = z3::fpa_get_sbits(*z3_ctx, sort);

                // sbits includes the sign bit and significand, mantissa is sbits - 1
                let fsort = FSort::new(ebits, sbits - 1);

                // Get the numeral value as a string and parse it
                let numeral_string = z3::get_numeral_string(*z3_ctx, *ast);
                let numeral_str = std::ffi::CStr::from_ptr(numeral_string).to_str().unwrap();

                // Parse the float value based on the sort
                if fsort == FSort::f32() {
                    let val = numeral_str.parse::<f32>().map_err(|_| {
                        ClarirsError::ConversionError("Failed to parse f32".to_string())
                    })?;
                    ctx.fpv(Float::F32(val))
                } else if fsort == FSort::f64() {
                    let val = numeral_str.parse::<f64>().map_err(|_| {
                        ClarirsError::ConversionError("Failed to parse f64".to_string())
                    })?;
                    ctx.fpv(Float::F64(val))
                } else {
                    // For other float sizes, use f64 as a fallback
                    let val = numeral_str.parse::<f64>().map_err(|_| {
                        ClarirsError::ConversionError("Failed to parse float".to_string())
                    })?;
                    ctx.fpv(Float::F64(val))
                }
            }
            z3::AstKind::App => {
                let app = z3::to_app(*z3_ctx, *ast);
                let decl = z3::get_app_decl(*z3_ctx, app);
                let decl_kind = z3::get_decl_kind(*z3_ctx, decl);
                let sort = z3::get_sort(*z3_ctx, *ast);
                let ebits = z3::fpa_get_ebits(*z3_ctx, sort);
                let sbits = z3::fpa_get_sbits(*z3_ctx, sort);
                let fsort = FSort::new(ebits, sbits - 1);

                match decl_kind {
                    // Z3 represents float numerals as FpaNum
                    z3::DeclKind::FpaNum => {
                        // Extract the float value from Z3
                        // For f32/f64, we can use get_numeral_double
                        if fsort == FSort::f32() {
                            let val = z3::get_numeral_double(*z3_ctx, *ast) as f32;
                            ctx.fpv(Float::F32(val))
                        } else if fsort == FSort::f64() {
                            let val = z3::get_numeral_double(*z3_ctx, *ast);
                            ctx.fpv(Float::F64(val))
                        } else {
                            // For other formats, use f64 as fallback
                            let val = z3::get_numeral_double(*z3_ctx, *ast);
                            ctx.fpv(Float::F64(val))
                        }
                    }
                    z3::DeclKind::Uninterpreted => {
                        let sym = z3::get_decl_name(*z3_ctx, decl);
                        let name = z3::get_symbol_string(*z3_ctx, sym);
                        let name = std::ffi::CStr::from_ptr(name).to_str().unwrap();
                        ctx.fps(name, fsort)
                    }
                    z3::DeclKind::FpaNeg => {
                        let arg = z3::get_app_arg(*z3_ctx, app, 0);
                        let inner = FloatAst::from_z3(ctx, arg)?;
                        ctx.fp_neg(&inner)
                    }
                    z3::DeclKind::FpaAbs => {
                        let arg = z3::get_app_arg(*z3_ctx, app, 0);
                        let inner = FloatAst::from_z3(ctx, arg)?;
                        ctx.fp_abs(&inner)
                    }
                    z3::DeclKind::FpaAdd
                    | z3::DeclKind::FpaSub
                    | z3::DeclKind::FpaMul
                    | z3::DeclKind::FpaDiv => {
                        let rm_arg = z3::get_app_arg(*z3_ctx, app, 0);
                        let arg0 = z3::get_app_arg(*z3_ctx, app, 1);
                        let arg1 = z3::get_app_arg(*z3_ctx, app, 2);

                        let rm = parse_fprm_from_z3(*z3_ctx, rm_arg)?;
                        let a = FloatAst::from_z3(ctx, arg0)?;
                        let b = FloatAst::from_z3(ctx, arg1)?;

                        match decl_kind {
                            z3::DeclKind::FpaAdd => ctx.fp_add(&a, &b, rm),
                            z3::DeclKind::FpaSub => ctx.fp_sub(&a, &b, rm),
                            z3::DeclKind::FpaMul => ctx.fp_mul(&a, &b, rm),
                            z3::DeclKind::FpaDiv => ctx.fp_div(&a, &b, rm),
                            _ => unreachable!(),
                        }
                    }
                    z3::DeclKind::FpaSqrt => {
                        let rm_arg = z3::get_app_arg(*z3_ctx, app, 0);
                        let arg = z3::get_app_arg(*z3_ctx, app, 1);

                        let rm = parse_fprm_from_z3(*z3_ctx, rm_arg)?;
                        let inner = FloatAst::from_z3(ctx, arg)?;
                        ctx.fp_sqrt(&inner, rm)
                    }
                    z3::DeclKind::FpaToFp => {
                        // This could be FpToFp, BvToFp, BvToFpSigned, or BvToFpUnsigned
                        let num_args = z3::get_app_num_args(*z3_ctx, app);

                        if num_args == 2 {
                            // Could be BvToFp (no rounding mode)
                            let arg = z3::get_app_arg(*z3_ctx, app, 0);
                            if let Ok(bv) = crate::astext::bv::from_z3(ctx, arg) {
                                ctx.bv_to_fp(&bv, fsort)
                            } else {
                                Err(ClarirsError::ConversionError(
                                    "Failed to parse BvToFp".to_string(),
                                ))
                            }
                        } else if num_args == 3 {
                            // Has rounding mode: FpToFp, BvToFpSigned, or BvToFpUnsigned
                            let rm_arg = z3::get_app_arg(*z3_ctx, app, 0);
                            let arg = z3::get_app_arg(*z3_ctx, app, 1);
                            let rm = parse_fprm_from_z3(*z3_ctx, rm_arg)?;

                            // Try to determine which conversion it is by the argument type
                            if let Ok(fp) = FloatAst::from_z3(ctx, arg) {
                                ctx.fp_to_fp(&fp, fsort, rm)
                            } else if let Ok(bv) = crate::astext::bv::from_z3(ctx, arg) {
                                // Need to determine if signed or unsigned
                                // This is ambiguous in Z3, default to signed
                                ctx.bv_to_fp_signed(&bv, fsort, rm)
                            } else {
                                Err(ClarirsError::ConversionError(
                                    "Failed to parse FpToFp conversion".to_string(),
                                ))
                            }
                        } else {
                            Err(ClarirsError::ConversionError(
                                "Unexpected number of arguments for FpaToFp".to_string(),
                            ))
                        }
                    }
                    z3::DeclKind::FpaFp => {
                        let sign = z3::get_app_arg(*z3_ctx, app, 0);
                        let exp = z3::get_app_arg(*z3_ctx, app, 1);
                        let sig = z3::get_app_arg(*z3_ctx, app, 2);

                        let sign_bv = crate::astext::bv::from_z3(ctx, sign)?;
                        let exp_bv = crate::astext::bv::from_z3(ctx, exp)?;
                        let sig_bv = crate::astext::bv::from_z3(ctx, sig)?;

                        ctx.fp_fp(&sign_bv, &exp_bv, &sig_bv)
                    }
                    z3::DeclKind::Ite => {
                        let cond = z3::get_app_arg(*z3_ctx, app, 0);
                        let then = z3::get_app_arg(*z3_ctx, app, 1);
                        let else_ = z3::get_app_arg(*z3_ctx, app, 2);
                        let cond = crate::astext::bool::from_z3(ctx, cond)?;
                        let then = FloatAst::from_z3(ctx, then)?;
                        let else_ = FloatAst::from_z3(ctx, else_)?;
                        ctx.if_(&cond, &then, &else_)
                    }
                    _ => Err(ClarirsError::ConversionError(
                        "Failed converting from z3: unknown decl kind for float".to_string(),
                    )),
                }
            }
            _ => Err(ClarirsError::ConversionError(
                "Failed converting from z3: unknown ast kind for float".to_string(),
            )),
        }
    })
}

fn parse_fprm_from_z3(z3_ctx: z3::Context, ast: z3::Ast) -> Result<FPRM, ClarirsError> {
    unsafe {
        let app = z3::to_app(z3_ctx, ast);
        let decl = z3::get_app_decl(z3_ctx, app);
        let decl_kind = z3::get_decl_kind(z3_ctx, decl);

        match decl_kind {
            z3::DeclKind::FpaRmNearestTiesToEven => Ok(FPRM::NearestTiesToEven),
            z3::DeclKind::FpaRmTowardPositive => Ok(FPRM::TowardPositive),
            z3::DeclKind::FpaRmTowardNegative => Ok(FPRM::TowardNegative),
            z3::DeclKind::FpaRmTowardZero => Ok(FPRM::TowardZero),
            z3::DeclKind::FpaRmNearestTiesToAway => Ok(FPRM::NearestTiesToAway),
            _ => Err(ClarirsError::ConversionError(
                "Unknown rounding mode".to_string(),
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn round_trip<'c>(
        ctx: &'c Context<'c>,
        ast: &FloatAst<'c>,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        match ast.to_z3() {
            Ok(z3_ast) => FloatAst::from_z3(ctx, z3_ast),
            Err(e) => Err(e),
        }
    }

    #[test]
    fn test_float_symbol() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f32()).unwrap();
        let result = round_trip(&ctx, &x).unwrap();
        assert_eq!(x, result);
    }

    #[test]
    fn test_float_value_f32() {
        let ctx = Context::new();
        let f = ctx.fpv(Float::F32(std::f32::consts::PI)).unwrap();
        let result = round_trip(&ctx, &f).unwrap();
        assert_eq!(f, result);
    }

    #[test]
    fn test_float_value_f64() {
        let ctx = Context::new();
        let f = ctx.fpv(Float::F64(std::f64::consts::E)).unwrap();
        let result = round_trip(&ctx, &f).unwrap();
        assert_eq!(f, result);
    }

    #[test]
    fn test_float_neg() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f32()).unwrap();
        let neg = ctx.fp_neg(&x).unwrap();
        let result = round_trip(&ctx, &neg).unwrap();
        assert_eq!(neg, result);
    }

    #[test]
    fn test_float_abs() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f32()).unwrap();
        let abs = ctx.fp_abs(&x).unwrap();
        let result = round_trip(&ctx, &abs).unwrap();
        assert_eq!(abs, result);
    }

    #[test]
    fn test_float_add() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let add = ctx.fp_add(&a, &b, FPRM::NearestTiesToEven).unwrap();
        let result = round_trip(&ctx, &add).unwrap();
        assert_eq!(add, result);
    }

    #[test]
    fn test_float_sub() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let sub = ctx.fp_sub(&a, &b, FPRM::NearestTiesToEven).unwrap();
        let result = round_trip(&ctx, &sub).unwrap();
        assert_eq!(sub, result);
    }

    #[test]
    fn test_float_mul() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let mul = ctx.fp_mul(&a, &b, FPRM::NearestTiesToEven).unwrap();
        let result = round_trip(&ctx, &mul).unwrap();
        assert_eq!(mul, result);
    }

    #[test]
    fn test_float_div() {
        let ctx = Context::new();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let div = ctx.fp_div(&a, &b, FPRM::NearestTiesToEven).unwrap();
        let result = round_trip(&ctx, &div).unwrap();
        assert_eq!(div, result);
    }

    #[test]
    fn test_float_sqrt() {
        let ctx = Context::new();
        let x = ctx.fps("x", FSort::f32()).unwrap();
        let sqrt = ctx.fp_sqrt(&x, FPRM::NearestTiesToEven).unwrap();
        let result = round_trip(&ctx, &sqrt).unwrap();
        assert_eq!(sqrt, result);
    }

    #[test]
    fn test_float_if() {
        let ctx = Context::new();
        let cond = ctx.bools("c").unwrap();
        let a = ctx.fps("a", FSort::f32()).unwrap();
        let b = ctx.fps("b", FSort::f32()).unwrap();
        let if_expr = ctx.if_(&cond, &a, &b).unwrap();
        let result = round_trip(&ctx, &if_expr).unwrap();
        assert_eq!(if_expr, result);
    }
}
