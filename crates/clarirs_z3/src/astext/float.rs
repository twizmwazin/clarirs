use clarirs_core::prelude::*;

use super::AstExtZ3;
use crate::{Z3_CONTEXT, astext::child, check_z3_error, rc::RcAst};
use z3_sys::*;

pub(crate) fn fprm_to_z3(rm: FPRM) -> Result<RcAst, ClarirsError> {
    RcAst::try_from(Z3_CONTEXT.with(|&z3_ctx| unsafe {
        match rm {
            FPRM::NearestTiesToEven => Z3_mk_fpa_rne(z3_ctx).expect("Z3_mk_fpa_rne returned null"),
            FPRM::TowardPositive => Z3_mk_fpa_rtp(z3_ctx).expect("Z3_mk_fpa_rtp returned null"),
            FPRM::TowardNegative => Z3_mk_fpa_rtn(z3_ctx).expect("Z3_mk_fpa_rtn returned null"),
            FPRM::TowardZero => Z3_mk_fpa_rtz(z3_ctx).expect("Z3_mk_fpa_rtz returned null"),
            FPRM::NearestTiesToAway => Z3_mk_fpa_rna(z3_ctx).expect("Z3_mk_fpa_rna returned null"),
        }
    }))
}

fn fsort_to_z3(sort: FSort) -> Z3_sort {
    Z3_CONTEXT.with(|&z3_ctx| unsafe {
        Z3_mk_fpa_sort(z3_ctx, sort.exponent, sort.mantissa + 1)
            .expect("Z3_mk_fpa_sort returned null")
    })
}

pub(crate) fn to_z3(ast: &FloatAst, children: &[RcAst]) -> Result<RcAst, ClarirsError> {
    Z3_CONTEXT.with(|&z3_ctx| unsafe {
        Ok(match ast.op() {
            FloatOp::FPS(s, sort) => {
                let s_cstr = std::ffi::CString::new(s.as_str()).unwrap();
                let sym = Z3_mk_string_symbol(z3_ctx, s_cstr.as_ptr())
                    .expect("Z3_mk_string_symbol returned null");
                let z3_sort = fsort_to_z3(*sort);
                RcAst::try_from(
                    Z3_mk_const(z3_ctx, sym, z3_sort).expect("Z3_mk_const returned null"),
                )?
            }
            FloatOp::FPV(f) => {
                let sort = fsort_to_z3(f.fsort());
                match f {
                    Float::F32(val) => RcAst::try_from(
                        Z3_mk_fpa_numeral_float(z3_ctx, *val, sort)
                            .expect("Z3_mk_fpa_numeral_float returned null"),
                    )?,
                    Float::F64(val) => RcAst::try_from(
                        Z3_mk_fpa_numeral_double(z3_ctx, *val, sort)
                            .expect("Z3_mk_fpa_numeral_double returned null"),
                    )?,
                }
            }
            FloatOp::FpNeg(..) => unop!(z3_ctx, children, Z3_mk_fpa_neg),
            FloatOp::FpAbs(..) => unop!(z3_ctx, children, Z3_mk_fpa_abs),
            FloatOp::FpAdd(_, _, rm) => {
                let rm_ast = fprm_to_z3(*rm)?;
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                RcAst::try_from(
                    Z3_mk_fpa_add(z3_ctx, *rm_ast, **a, **b).expect("Z3_mk_fpa_add returned null"),
                )?
            }
            FloatOp::FpSub(_, _, rm) => {
                let rm_ast = fprm_to_z3(*rm)?;
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                RcAst::try_from(
                    Z3_mk_fpa_sub(z3_ctx, *rm_ast, **a, **b).expect("Z3_mk_fpa_sub returned null"),
                )?
            }
            FloatOp::FpMul(_, _, rm) => {
                let rm_ast = fprm_to_z3(*rm)?;
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                RcAst::try_from(
                    Z3_mk_fpa_mul(z3_ctx, *rm_ast, **a, **b).expect("Z3_mk_fpa_mul returned null"),
                )?
            }
            FloatOp::FpDiv(_, _, rm) => {
                let rm_ast = fprm_to_z3(*rm)?;
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                RcAst::try_from(
                    Z3_mk_fpa_div(z3_ctx, *rm_ast, **a, **b).expect("Z3_mk_fpa_div returned null"),
                )?
            }
            FloatOp::FpSqrt(_, rm) => {
                let rm_ast = fprm_to_z3(*rm)?;
                let a = child(children, 0)?;
                RcAst::try_from(
                    Z3_mk_fpa_sqrt(z3_ctx, *rm_ast, **a).expect("Z3_mk_fpa_sqrt returned null"),
                )?
            }
            FloatOp::FpToFp(_, sort, rm) => {
                let rm_ast = fprm_to_z3(*rm)?;
                let a = child(children, 0)?;
                let z3_sort = fsort_to_z3(*sort);
                RcAst::try_from(
                    Z3_mk_fpa_to_fp_float(z3_ctx, *rm_ast, **a, z3_sort)
                        .expect("Z3_mk_fpa_to_fp_float returned null"),
                )?
            }
            FloatOp::FpFP(..) => {
                let sign = child(children, 0)?;
                let exp = child(children, 1)?;
                let sig = child(children, 2)?;
                RcAst::try_from(
                    Z3_mk_fpa_fp(z3_ctx, **sign, **exp, **sig).expect("Z3_mk_fpa_fp returned null"),
                )?
            }
            FloatOp::BvToFp(_, sort) => {
                let a = child(children, 0)?;
                let z3_sort = fsort_to_z3(*sort);
                RcAst::try_from(
                    Z3_mk_fpa_to_fp_bv(z3_ctx, **a, z3_sort)
                        .expect("Z3_mk_fpa_to_fp_bv returned null"),
                )?
            }
            FloatOp::BvToFpSigned(_, sort, rm) => {
                let rm_ast = fprm_to_z3(*rm)?;
                let a = child(children, 0)?;
                let z3_sort = fsort_to_z3(*sort);
                RcAst::try_from(
                    Z3_mk_fpa_to_fp_signed(z3_ctx, *rm_ast, **a, z3_sort)
                        .expect("Z3_mk_fpa_to_fp_signed returned null"),
                )?
            }
            FloatOp::BvToFpUnsigned(_, sort, rm) => {
                let rm_ast = fprm_to_z3(*rm)?;
                let a = child(children, 0)?;
                let z3_sort = fsort_to_z3(*sort);
                RcAst::try_from(
                    Z3_mk_fpa_to_fp_unsigned(z3_ctx, *rm_ast, **a, z3_sort)
                        .expect("Z3_mk_fpa_to_fp_unsigned returned null"),
                )?
            }
            FloatOp::ITE(..) => {
                let cond = child(children, 0)?;
                let then = child(children, 1)?;
                let else_ = child(children, 2)?;
                RcAst::try_from(
                    Z3_mk_ite(z3_ctx, **cond, **then, **else_).expect("Z3_mk_ite returned null"),
                )?
            }
        })
        .and_then(|maybe_null| {
            check_z3_error()?;
            Ok(maybe_null)
        })
    })
}

pub(crate) fn from_z3<'c>(
    ctx: &'c Context<'c>,
    ast: impl Into<RcAst>,
) -> Result<FloatAst<'c>, ClarirsError> {
    Z3_CONTEXT.with(|z3_ctx| unsafe {
        let ast = ast.into();
        let ast_kind = Z3_get_ast_kind(*z3_ctx, *ast);
        match ast_kind {
            AstKind::Numeral => {
                // Get the sort to determine if it's f32 or f64
                let sort = Z3_get_sort(*z3_ctx, *ast).expect("Z3_get_sort returned null");
                let ebits = Z3_fpa_get_ebits(*z3_ctx, sort);
                let sbits = Z3_fpa_get_sbits(*z3_ctx, sort);

                // sbits includes the sign bit and significand, mantissa is sbits - 1
                let fsort = FSort::new(ebits, sbits - 1);

                // Get the numeral value as a string and parse it
                let numeral_string = Z3_get_numeral_string(*z3_ctx, *ast);
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
            AstKind::App => {
                let app = Z3_to_app(*z3_ctx, *ast).expect("Z3_to_app returned null");
                let decl = Z3_get_app_decl(*z3_ctx, app).expect("Z3_get_app_decl returned null");
                let decl_kind = Z3_get_decl_kind(*z3_ctx, decl);
                let sort = Z3_get_sort(*z3_ctx, *ast).expect("Z3_get_sort returned null");
                let ebits = Z3_fpa_get_ebits(*z3_ctx, sort);
                let sbits = Z3_fpa_get_sbits(*z3_ctx, sort);
                let fsort = FSort::new(ebits, sbits - 1);

                match decl_kind {
                    // Z3 represents float numerals as FpaNum
                    DeclKind::FPA_NUM => {
                        // Extract the float value from Z3
                        // For f32/f64, we can use get_numeral_double
                        if fsort == FSort::f32() {
                            let val = Z3_get_numeral_double(*z3_ctx, *ast) as f32;
                            ctx.fpv(Float::F32(val))
                        } else if fsort == FSort::f64() {
                            let val = Z3_get_numeral_double(*z3_ctx, *ast);
                            ctx.fpv(Float::F64(val))
                        } else {
                            // For other formats, use f64 as fallback
                            let val = Z3_get_numeral_double(*z3_ctx, *ast);
                            ctx.fpv(Float::F64(val))
                        }
                    }
                    DeclKind::FPA_NAN => {
                        if fsort == FSort::f32() {
                            return ctx.fpv(Float::F32(f32::NAN));
                        }
                        ctx.fpv(Float::F64(f64::NAN))
                    }
                    DeclKind::UNINTERPRETED => {
                        let sym = Z3_get_decl_name(*z3_ctx, decl)
                            .expect("Z3_get_decl_name returned null");
                        let name = Z3_get_symbol_string(*z3_ctx, sym);
                        let name = std::ffi::CStr::from_ptr(name).to_str().unwrap();
                        ctx.fps(name, fsort)
                    }
                    DeclKind::FPA_NEG => {
                        let arg = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let inner = FloatAst::from_z3(ctx, arg)?;
                        ctx.fp_neg(inner)
                    }
                    DeclKind::FPA_ABS => {
                        let arg = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let inner = FloatAst::from_z3(ctx, arg)?;
                        ctx.fp_abs(inner)
                    }
                    DeclKind::FPA_ADD
                    | DeclKind::FPA_SUB
                    | DeclKind::FPA_MUL
                    | DeclKind::FPA_DIV => {
                        let rm_arg = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let arg0 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"),
                        )?;
                        let arg1 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 2).expect("Z3_get_app_arg returned null"),
                        )?;

                        let rm = parse_fprm_from_z3(*z3_ctx, *rm_arg)?;
                        let a = FloatAst::from_z3(ctx, arg0)?;
                        let b = FloatAst::from_z3(ctx, arg1)?;

                        match decl_kind {
                            DeclKind::FPA_ADD => ctx.fp_add(a, b, rm),
                            DeclKind::FPA_SUB => ctx.fp_sub(a, b, rm),
                            DeclKind::FPA_MUL => ctx.fp_mul(a, b, rm),
                            DeclKind::FPA_DIV => ctx.fp_div(a, b, rm),
                            _ => unreachable!(),
                        }
                    }
                    DeclKind::FPA_SQRT => {
                        let rm_arg = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let arg = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"),
                        )?;

                        let rm = parse_fprm_from_z3(*z3_ctx, *rm_arg)?;
                        let inner = FloatAst::from_z3(ctx, arg)?;
                        ctx.fp_sqrt(inner, rm)
                    }
                    DeclKind::FPA_TO_FP => {
                        // Z3 uses FpaToFp for several conversions:
                        //   1 arg:  BvToFp(bv)           -- reinterpret BV bits as FP
                        //   2 args: [rm, fp] -> FpToFp    -- convert between FP sorts
                        //           [rm, bv] -> BvToFpSigned -- signed int to FP
                        let num_args = Z3_get_app_num_args(*z3_ctx, app);

                        if num_args == 1 {
                            // BvToFp: no rounding mode, single BV operand
                            let arg = RcAst::try_from(
                                Z3_get_app_arg(*z3_ctx, app, 0)
                                    .expect("Z3_get_app_arg returned null"),
                            )?;
                            let bv = crate::astext::bv::from_z3(ctx, arg)?;
                            ctx.bv_to_fp(bv, fsort)
                        } else if num_args == 2 {
                            // Has rounding mode as arg0, operand as arg1
                            let rm_arg = RcAst::try_from(
                                Z3_get_app_arg(*z3_ctx, app, 0)
                                    .expect("Z3_get_app_arg returned null"),
                            )?;
                            let arg = RcAst::try_from(
                                Z3_get_app_arg(*z3_ctx, app, 1)
                                    .expect("Z3_get_app_arg returned null"),
                            )?;
                            let rm = parse_fprm_from_z3(*z3_ctx, *rm_arg)?;

                            // Use sort-kind of the operand to determine FP vs BV
                            let arg_sort =
                                Z3_get_sort(*z3_ctx, *arg).expect("Z3_get_sort returned null");
                            let sort_kind = Z3_get_sort_kind(*z3_ctx, arg_sort);
                            match sort_kind {
                                SortKind::FloatingPoint => {
                                    let fp = FloatAst::from_z3(ctx, arg)?;
                                    ctx.fp_to_fp(fp, fsort, rm)
                                }
                                SortKind::BV => {
                                    let bv = crate::astext::bv::from_z3(ctx, arg)?;
                                    ctx.bv_to_fp_signed(bv, fsort, rm)
                                }
                                _ => Err(ClarirsError::ConversionError(
                                    "FpaToFp: unexpected sort kind for operand".to_string(),
                                )),
                            }
                        } else {
                            Err(ClarirsError::ConversionError(
                                "Unexpected number of arguments for FpaToFp".to_string(),
                            ))
                        }
                    }
                    DeclKind::FPA_FP => {
                        let sign = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let exp = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"),
                        )?;
                        let sig = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 2).expect("Z3_get_app_arg returned null"),
                        )?;

                        let sign_bv = crate::astext::bv::from_z3(ctx, sign)?;
                        let exp_bv = crate::astext::bv::from_z3(ctx, exp)?;
                        let sig_bv = crate::astext::bv::from_z3(ctx, sig)?;

                        ctx.fp_fp(sign_bv, exp_bv, sig_bv)
                    }
                    DeclKind::ITE => {
                        let cond = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let then = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"),
                        )?;
                        let else_ = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 2).expect("Z3_get_app_arg returned null"),
                        )?;
                        let cond = crate::astext::bool::from_z3(ctx, cond)?;
                        let then = FloatAst::from_z3(ctx, then)?;
                        let else_ = FloatAst::from_z3(ctx, else_)?;
                        ctx.ite(cond, then, else_)
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

fn parse_fprm_from_z3(z3_ctx: Z3_context, ast: Z3_ast) -> Result<FPRM, ClarirsError> {
    unsafe {
        let app = Z3_to_app(z3_ctx, ast).expect("Z3_to_app returned null");
        let decl = Z3_get_app_decl(z3_ctx, app).expect("Z3_get_app_decl returned null");
        let decl_kind = Z3_get_decl_kind(z3_ctx, decl);

        match decl_kind {
            DeclKind::FPA_RM_NEAREST_TIES_TO_EVEN => Ok(FPRM::NearestTiesToEven),
            DeclKind::FPA_RM_TOWARD_POSITIVE => Ok(FPRM::TowardPositive),
            DeclKind::FPA_RM_TOWARD_NEGATIVE => Ok(FPRM::TowardNegative),
            DeclKind::FPA_RM_TOWARD_ZERO => Ok(FPRM::TowardZero),
            DeclKind::FPA_RM_NEAREST_TIES_TO_AWAY => Ok(FPRM::NearestTiesToAway),
            _ => Err(ClarirsError::ConversionError(
                "Unknown rounding mode".to_string(),
            )),
        }
    }
}
