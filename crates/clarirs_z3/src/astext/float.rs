use clarirs_core::prelude::*;
use z3::ast::{Ast, Dynamic, Float, RoundingMode};

use super::AstExtZ3;
use crate::astext::child;

pub(crate) fn fprm_to_z3(rm: FPRM) -> Result<RoundingMode, ClarirsError> {
    Ok(match rm {
        FPRM::NearestTiesToEven => RoundingMode::round_nearest_ties_to_even(),
        FPRM::TowardPositive => RoundingMode::round_towards_positive(),
        FPRM::TowardNegative => RoundingMode::round_towards_negative(),
        FPRM::TowardZero => RoundingMode::round_towards_zero(),
        FPRM::NearestTiesToAway => RoundingMode::round_nearest_ties_to_away(),
    })
}

/// Create a float from sign, exponent, and significand bitvectors using z3-sys.
pub(crate) fn float_from_sign_exp_sig(
    sign: &z3::ast::BV,
    exp: &z3::ast::BV,
    sig: &z3::ast::BV,
) -> Dynamic {
    let ctx = sign.get_ctx();
    unsafe {
        Dynamic::wrap(
            ctx,
            z3_sys::Z3_mk_fpa_fp(
                ctx.get_z3_context(),
                sign.get_z3_ast(),
                exp.get_z3_ast(),
                sig.get_z3_ast(),
            )
            .unwrap(),
        )
    }
}

/// Create a Z3 floating-point sort with the given exponent and significand bit widths.
unsafe fn mk_fpa_sort(z3_ctx: z3_sys::Z3_context, ebits: u32, sbits: u32) -> z3_sys::Z3_sort {
    z3_sys::Z3_mk_fpa_sort(z3_ctx, ebits, sbits).unwrap()
}

/// Interpret a bitvector as a float of the given sort using z3-sys.
fn float_from_bv(bv: &z3::ast::BV, ebits: u32, sbits: u32) -> Dynamic {
    let ctx = bv.get_ctx();
    unsafe {
        let z3_ctx = ctx.get_z3_context();
        Dynamic::wrap(
            ctx,
            z3_sys::Z3_mk_fpa_to_fp_bv(z3_ctx, bv.get_z3_ast(), mk_fpa_sort(z3_ctx, ebits, sbits))
                .unwrap(),
        )
    }
}

/// Convert a signed bitvector to float with rounding mode using z3-sys.
fn signed_bv_to_float(bv: &z3::ast::BV, rm: &RoundingMode, ebits: u32, sbits: u32) -> Dynamic {
    let ctx = bv.get_ctx();
    unsafe {
        let z3_ctx = ctx.get_z3_context();
        Dynamic::wrap(
            ctx,
            z3_sys::Z3_mk_fpa_to_fp_signed(
                z3_ctx,
                rm.get_z3_ast(),
                bv.get_z3_ast(),
                mk_fpa_sort(z3_ctx, ebits, sbits),
            )
            .unwrap(),
        )
    }
}

/// Convert an unsigned bitvector to float with rounding mode using z3-sys.
fn unsigned_bv_to_float(bv: &z3::ast::BV, rm: &RoundingMode, ebits: u32, sbits: u32) -> Dynamic {
    let ctx = bv.get_ctx();
    unsafe {
        let z3_ctx = ctx.get_z3_context();
        Dynamic::wrap(
            ctx,
            z3_sys::Z3_mk_fpa_to_fp_unsigned(
                z3_ctx,
                rm.get_z3_ast(),
                bv.get_z3_ast(),
                mk_fpa_sort(z3_ctx, ebits, sbits),
            )
            .unwrap(),
        )
    }
}

pub(crate) fn to_z3(ast: &FloatAst, children: &[Dynamic]) -> Result<Dynamic, ClarirsError> {
    Ok(match ast.op() {
        FloatOp::FPS(s, sort) => Dynamic::from(Float::new_const(
            s.as_str(),
            sort.exponent,
            sort.mantissa + 1,
        )),
        FloatOp::FPV(f) => match f {
            clarirs_core::prelude::Float::F32(val) => Dynamic::from(Float::from_f32(*val)),
            clarirs_core::prelude::Float::F64(val) => Dynamic::from(Float::from_f64(*val)),
        },
        FloatOp::FpNeg(..) => Dynamic::from(child(children, 0)?.as_float().unwrap().unary_neg()),
        FloatOp::FpAbs(..) => Dynamic::from(child(children, 0)?.as_float().unwrap().unary_abs()),
        FloatOp::FpAdd(_, _, rm)
        | FloatOp::FpSub(_, _, rm)
        | FloatOp::FpMul(_, _, rm)
        | FloatOp::FpDiv(_, _, rm) => {
            let rm_ast = fprm_to_z3(*rm)?;
            let a = child(children, 0)?.as_float().unwrap();
            let b = child(children, 1)?.as_float().unwrap();
            Dynamic::from(match ast.op() {
                FloatOp::FpAdd(..) => a.add_with_rounding_mode(&b, &rm_ast),
                FloatOp::FpSub(..) => a.sub_with_rounding_mode(&b, &rm_ast),
                FloatOp::FpMul(..) => a.mul_with_rounding_mode(&b, &rm_ast),
                FloatOp::FpDiv(..) => a.div_with_rounding_mode(&b, &rm_ast),
                _ => unreachable!(),
            })
        }
        FloatOp::FpSqrt(_, rm) => Dynamic::from(
            child(children, 0)?
                .as_float()
                .unwrap()
                .sqrt_with_rounding_mode(&fprm_to_z3(*rm)?),
        ),
        FloatOp::FpToFp(_, sort, rm) => {
            let rm_ast = fprm_to_z3(*rm)?;
            let a = child(children, 0)?.as_float().unwrap();
            let z3_sort = z3::Sort::float(sort.exponent, sort.mantissa + 1);
            Dynamic::from(a.to_fp_with_rounding_mode(&rm_ast, &z3_sort))
        }
        FloatOp::FpFP(..) => {
            let sign = child(children, 0)?.as_bv().unwrap();
            let exp = child(children, 1)?.as_bv().unwrap();
            let sig = child(children, 2)?.as_bv().unwrap();
            float_from_sign_exp_sig(&sign, &exp, &sig)
        }
        FloatOp::BvToFp(_, sort) => {
            let a = child(children, 0)?.as_bv().unwrap();
            float_from_bv(&a, sort.exponent, sort.mantissa + 1)
        }
        FloatOp::BvToFpSigned(_, sort, rm) => {
            let rm_ast = fprm_to_z3(*rm)?;
            let a = child(children, 0)?.as_bv().unwrap();
            signed_bv_to_float(&a, &rm_ast, sort.exponent, sort.mantissa + 1)
        }
        FloatOp::BvToFpUnsigned(_, sort, rm) => {
            let rm_ast = fprm_to_z3(*rm)?;
            let a = child(children, 0)?.as_bv().unwrap();
            unsigned_bv_to_float(&a, &rm_ast, sort.exponent, sort.mantissa + 1)
        }
        FloatOp::ITE(..) => {
            let cond = child(children, 0)?.as_bool().unwrap();
            let then = child(children, 1)?;
            let else_ = child(children, 2)?;
            cond.ite(then, else_)
        }
    })
}

pub(crate) fn from_z3<'c>(
    ctx: &'c Context<'c>,
    ast: Dynamic,
) -> Result<FloatAst<'c>, ClarirsError> {
    let ast_kind = ast.kind();
    match ast_kind {
        z3::AstKind::Numeral => {
            let fp = ast.as_float().ok_or_else(|| {
                ClarirsError::ConversionError("expected float numeral".to_string())
            })?;
            let sort = fp.get_sort();
            let ebits = sort.float_exponent_size().unwrap();
            let sbits = sort.float_significand_size().unwrap();
            let fsort = FSort::new(ebits, sbits - 1);

            let numeral_str = format!("{ast}");
            if fsort == FSort::f32() {
                let val = numeral_str.parse::<f32>().map_err(|_| {
                    ClarirsError::ConversionError("Failed to parse f32".to_string())
                })?;
                ctx.fpv(clarirs_core::prelude::Float::F32(val))
            } else if fsort == FSort::f64() {
                let val = numeral_str.parse::<f64>().map_err(|_| {
                    ClarirsError::ConversionError("Failed to parse f64".to_string())
                })?;
                ctx.fpv(clarirs_core::prelude::Float::F64(val))
            } else {
                let val = numeral_str.parse::<f64>().map_err(|_| {
                    ClarirsError::ConversionError("Failed to parse float".to_string())
                })?;
                ctx.fpv(clarirs_core::prelude::Float::F64(val))
            }
        }
        z3::AstKind::App => {
            let decl = ast
                .safe_decl()
                .map_err(|_| ClarirsError::ConversionError("not an app".to_string()))?;
            let decl_kind = decl.kind();
            let fp = ast
                .as_float()
                .ok_or_else(|| ClarirsError::ConversionError("expected float sort".to_string()))?;
            let sort = fp.get_sort();
            let ebits = sort.float_exponent_size().unwrap();
            let sbits = sort.float_significand_size().unwrap();
            let fsort = FSort::new(ebits, sbits - 1);

            match decl_kind {
                z3::DeclKind::FPA_NUM => {
                    let val = fp.as_f64();
                    if fsort == FSort::f32() {
                        ctx.fpv(clarirs_core::prelude::Float::F32(val as f32))
                    } else {
                        ctx.fpv(clarirs_core::prelude::Float::F64(val))
                    }
                }
                z3::DeclKind::FPA_NAN => {
                    if fsort == FSort::f32() {
                        return ctx.fpv(clarirs_core::prelude::Float::F32(f32::NAN));
                    }
                    ctx.fpv(clarirs_core::prelude::Float::F64(f64::NAN))
                }
                z3::DeclKind::UNINTERPRETED => {
                    let name = decl.name();
                    ctx.fps(&name, fsort)
                }
                z3::DeclKind::FPA_NEG => {
                    let inner = FloatAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    ctx.fp_neg(inner)
                }
                z3::DeclKind::FPA_ABS => {
                    let inner = FloatAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    ctx.fp_abs(inner)
                }
                z3::DeclKind::FPA_ADD
                | z3::DeclKind::FPA_SUB
                | z3::DeclKind::FPA_MUL
                | z3::DeclKind::FPA_DIV => {
                    let rm = parse_fprm_from_z3(&ast.nth_child(0).unwrap())?;
                    let a = FloatAst::from_z3(ctx, ast.nth_child(1).unwrap())?;
                    let b = FloatAst::from_z3(ctx, ast.nth_child(2).unwrap())?;

                    match decl_kind {
                        z3::DeclKind::FPA_ADD => ctx.fp_add(a, b, rm),
                        z3::DeclKind::FPA_SUB => ctx.fp_sub(a, b, rm),
                        z3::DeclKind::FPA_MUL => ctx.fp_mul(a, b, rm),
                        z3::DeclKind::FPA_DIV => ctx.fp_div(a, b, rm),
                        _ => unreachable!(),
                    }
                }
                z3::DeclKind::FPA_SQRT => {
                    let rm = parse_fprm_from_z3(&ast.nth_child(0).unwrap())?;
                    let inner = FloatAst::from_z3(ctx, ast.nth_child(1).unwrap())?;
                    ctx.fp_sqrt(inner, rm)
                }
                z3::DeclKind::FPA_TO_FP => {
                    let num_args = ast.num_children();

                    if num_args == 1 {
                        let bv = crate::astext::bv::from_z3(ctx, ast.nth_child(0).unwrap())?;
                        ctx.bv_to_fp(bv, fsort)
                    } else if num_args == 2 {
                        let rm = parse_fprm_from_z3(&ast.nth_child(0).unwrap())?;
                        let arg = ast.nth_child(1).unwrap();
                        let sort_kind = arg.sort_kind();
                        match sort_kind {
                            z3::SortKind::FloatingPoint => {
                                let fp_inner = FloatAst::from_z3(ctx, arg)?;
                                ctx.fp_to_fp(fp_inner, fsort, rm)
                            }
                            z3::SortKind::BV => {
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
                z3::DeclKind::FPA_FP => {
                    let sign_bv = crate::astext::bv::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let exp_bv = crate::astext::bv::from_z3(ctx, ast.nth_child(1).unwrap())?;
                    let sig_bv = crate::astext::bv::from_z3(ctx, ast.nth_child(2).unwrap())?;
                    ctx.fp_fp(sign_bv, exp_bv, sig_bv)
                }
                z3::DeclKind::ITE => {
                    let cond = crate::astext::bool::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let then = FloatAst::from_z3(ctx, ast.nth_child(1).unwrap())?;
                    let else_ = FloatAst::from_z3(ctx, ast.nth_child(2).unwrap())?;
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
}

fn parse_fprm_from_z3(ast: &Dynamic) -> Result<FPRM, ClarirsError> {
    let decl = ast
        .safe_decl()
        .map_err(|_| ClarirsError::ConversionError("rounding mode is not an app".to_string()))?;
    let decl_kind = decl.kind();

    match decl_kind {
        z3::DeclKind::FPA_RM_NEAREST_TIES_TO_EVEN => Ok(FPRM::NearestTiesToEven),
        z3::DeclKind::FPA_RM_TOWARD_POSITIVE => Ok(FPRM::TowardPositive),
        z3::DeclKind::FPA_RM_TOWARD_NEGATIVE => Ok(FPRM::TowardNegative),
        z3::DeclKind::FPA_RM_TOWARD_ZERO => Ok(FPRM::TowardZero),
        z3::DeclKind::FPA_RM_NEAREST_TIES_TO_AWAY => Ok(FPRM::NearestTiesToAway),
        _ => Err(ClarirsError::ConversionError(
            "Unknown rounding mode".to_string(),
        )),
    }
}
