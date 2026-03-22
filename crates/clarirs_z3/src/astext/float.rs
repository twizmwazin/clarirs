use clarirs_core::prelude::*;
use z3::ast::{Ast, Dynamic, Float, RoundingMode};

use super::AstExtZ3;
use crate::astext::{DynamicExt, child};

pub(crate) fn fprm_to_z3(rm: FPRM) -> Result<RoundingMode, ClarirsError> {
    Ok(match rm {
        FPRM::NearestTiesToEven => RoundingMode::round_nearest_ties_to_even(),
        FPRM::TowardPositive => RoundingMode::round_towards_positive(),
        FPRM::TowardNegative => RoundingMode::round_towards_negative(),
        FPRM::TowardZero => RoundingMode::round_towards_zero(),
        FPRM::NearestTiesToAway => RoundingMode::round_nearest_ties_to_away(),
    })
}

pub(crate) fn float_from_sign_exp_sig(
    sign: &z3::ast::BV,
    exp: &z3::ast::BV,
    sig: &z3::ast::BV,
) -> Dynamic {
    let ctx = sign.get_ctx();
    unsafe {
        // z3-sys unwraps are safe here: these are well-formed Z3 AST operations
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

unsafe fn mk_fpa_sort(z3_ctx: z3_sys::Z3_context, ebits: u32, sbits: u32) -> z3_sys::Z3_sort {
    // unwrap is safe: valid Z3 context with valid bit widths
    z3_sys::Z3_mk_fpa_sort(z3_ctx, ebits, sbits).unwrap()
}

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
        FloatOp::FpNeg(..) => Dynamic::from(child(children, 0)?.to_float()?.unary_neg()),
        FloatOp::FpAbs(..) => Dynamic::from(child(children, 0)?.to_float()?.unary_abs()),
        FloatOp::FpAdd(_, _, rm)
        | FloatOp::FpSub(_, _, rm)
        | FloatOp::FpMul(_, _, rm)
        | FloatOp::FpDiv(_, _, rm) => {
            let rm_ast = fprm_to_z3(*rm)?;
            let a = child(children, 0)?.to_float()?;
            let b = child(children, 1)?.to_float()?;
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
                .to_float()?
                .sqrt_with_rounding_mode(&fprm_to_z3(*rm)?),
        ),
        FloatOp::FpToFp(_, sort, rm) => {
            let rm_ast = fprm_to_z3(*rm)?;
            let a = child(children, 0)?.to_float()?;
            let z3_sort = z3::Sort::float(sort.exponent, sort.mantissa + 1);
            Dynamic::from(a.to_fp_with_rounding_mode(&rm_ast, &z3_sort))
        }
        FloatOp::FpFP(..) => {
            let sign = child(children, 0)?.to_bv()?;
            let exp = child(children, 1)?.to_bv()?;
            let sig = child(children, 2)?.to_bv()?;
            float_from_sign_exp_sig(&sign, &exp, &sig)
        }
        FloatOp::BvToFp(_, sort) => float_from_bv(
            &child(children, 0)?.to_bv()?,
            sort.exponent,
            sort.mantissa + 1,
        ),
        FloatOp::BvToFpSigned(_, sort, rm) => {
            let rm_ast = fprm_to_z3(*rm)?;
            signed_bv_to_float(
                &child(children, 0)?.to_bv()?,
                &rm_ast,
                sort.exponent,
                sort.mantissa + 1,
            )
        }
        FloatOp::BvToFpUnsigned(_, sort, rm) => {
            let rm_ast = fprm_to_z3(*rm)?;
            unsigned_bv_to_float(
                &child(children, 0)?.to_bv()?,
                &rm_ast,
                sort.exponent,
                sort.mantissa + 1,
            )
        }
        FloatOp::ITE(..) => child(children, 0)?
            .to_bool()?
            .ite(child(children, 1)?, child(children, 2)?),
    })
}

fn get_fsort(fp: &Float) -> Result<FSort, ClarirsError> {
    let sort = fp.get_sort();
    let ebits = sort
        .float_exponent_size()
        .ok_or_else(|| ClarirsError::ConversionError("failed to get float exponent size".into()))?;
    let sbits = sort.float_significand_size().ok_or_else(|| {
        ClarirsError::ConversionError("failed to get float significand size".into())
    })?;
    Ok(FSort::new(ebits, sbits - 1))
}

pub(crate) fn from_z3<'c>(
    ctx: &'c Context<'c>,
    ast: Dynamic,
) -> Result<FloatAst<'c>, ClarirsError> {
    let ast_kind = ast.kind();
    match ast_kind {
        z3::AstKind::Numeral => {
            let fp = ast.to_float()?;
            let fsort = get_fsort(&fp)?;
            let numeral_str = format!("{ast}");
            if fsort == FSort::f32() {
                let val = numeral_str
                    .parse::<f32>()
                    .map_err(|_| ClarirsError::ConversionError("Failed to parse f32".into()))?;
                ctx.fpv(clarirs_core::prelude::Float::F32(val))
            } else {
                let val = numeral_str
                    .parse::<f64>()
                    .map_err(|_| ClarirsError::ConversionError("Failed to parse f64".into()))?;
                ctx.fpv(clarirs_core::prelude::Float::F64(val))
            }
        }
        z3::AstKind::App => {
            let decl = ast.get_decl()?;
            let decl_kind = decl.kind();

            match decl_kind {
                z3::DeclKind::FPA_NUM => {
                    let fp = ast.to_float()?;
                    let fsort = get_fsort(&fp)?;
                    let val = fp.as_f64();
                    if fsort == FSort::f32() {
                        ctx.fpv(clarirs_core::prelude::Float::F32(val as f32))
                    } else {
                        ctx.fpv(clarirs_core::prelude::Float::F64(val))
                    }
                }
                z3::DeclKind::FPA_NAN => {
                    let fsort = get_fsort(&ast.to_float()?)?;
                    if fsort == FSort::f32() {
                        return ctx.fpv(clarirs_core::prelude::Float::F32(f32::NAN));
                    }
                    ctx.fpv(clarirs_core::prelude::Float::F64(f64::NAN))
                }
                z3::DeclKind::UNINTERPRETED => {
                    let fsort = get_fsort(&ast.to_float()?)?;
                    ctx.fps(&decl.name(), fsort)
                }
                z3::DeclKind::FPA_NEG => ctx.fp_neg(FloatAst::from_z3(ctx, ast.nth(0)?)?),
                z3::DeclKind::FPA_ABS => ctx.fp_abs(FloatAst::from_z3(ctx, ast.nth(0)?)?),
                z3::DeclKind::FPA_ADD
                | z3::DeclKind::FPA_SUB
                | z3::DeclKind::FPA_MUL
                | z3::DeclKind::FPA_DIV => {
                    let rm = parse_fprm_from_z3(&ast.nth(0)?)?;
                    let a = FloatAst::from_z3(ctx, ast.nth(1)?)?;
                    let b = FloatAst::from_z3(ctx, ast.nth(2)?)?;
                    match decl_kind {
                        z3::DeclKind::FPA_ADD => ctx.fp_add(a, b, rm),
                        z3::DeclKind::FPA_SUB => ctx.fp_sub(a, b, rm),
                        z3::DeclKind::FPA_MUL => ctx.fp_mul(a, b, rm),
                        z3::DeclKind::FPA_DIV => ctx.fp_div(a, b, rm),
                        _ => unreachable!(),
                    }
                }
                z3::DeclKind::FPA_SQRT => {
                    let rm = parse_fprm_from_z3(&ast.nth(0)?)?;
                    ctx.fp_sqrt(FloatAst::from_z3(ctx, ast.nth(1)?)?, rm)
                }
                z3::DeclKind::FPA_TO_FP => {
                    let num_args = ast.num_children();
                    if num_args == 1 {
                        let bv = crate::astext::bv::from_z3(ctx, ast.nth(0)?)?;
                        ctx.bv_to_fp(bv, fsort)
                    } else if num_args == 2 {
                        let rm = parse_fprm_from_z3(&ast.nth(0)?)?;
                        let arg = ast.nth(1)?;
                        match arg.sort_kind() {
                            z3::SortKind::FloatingPoint => {
                                ctx.fp_to_fp(FloatAst::from_z3(ctx, arg)?, fsort, rm)
                            }
                            z3::SortKind::BV => ctx.bv_to_fp_signed(
                                crate::astext::bv::from_z3(ctx, arg)?,
                                fsort,
                                rm,
                            ),
                            _ => Err(ClarirsError::ConversionError(
                                "FpaToFp: unexpected sort kind for operand".into(),
                            )),
                        }
                    } else {
                        Err(ClarirsError::ConversionError(
                            "Unexpected number of arguments for FpaToFp".into(),
                        ))
                    }
                }
                z3::DeclKind::FPA_FP => {
                    let sign_bv = crate::astext::bv::from_z3(ctx, ast.nth(0)?)?;
                    let exp_bv = crate::astext::bv::from_z3(ctx, ast.nth(1)?)?;
                    let sig_bv = crate::astext::bv::from_z3(ctx, ast.nth(2)?)?;
                    ctx.fp_fp(sign_bv, exp_bv, sig_bv)
                }
                z3::DeclKind::ITE => {
                    let cond = crate::astext::bool::from_z3(ctx, ast.nth(0)?)?;
                    let then = FloatAst::from_z3(ctx, ast.nth(1)?)?;
                    let else_ = FloatAst::from_z3(ctx, ast.nth(2)?)?;
                    ctx.ite(cond, then, else_)
                }
                _ => Err(ClarirsError::ConversionError(
                    "Failed converting from z3: unknown decl kind for float".into(),
                )),
            }
        }
        _ => Err(ClarirsError::ConversionError(
            "Failed converting from z3: unknown ast kind for float".into(),
        )),
    }
}

fn parse_fprm_from_z3(ast: &Dynamic) -> Result<FPRM, ClarirsError> {
    let decl = ast.get_decl()?;
    match decl.kind() {
        z3::DeclKind::FPA_RM_NEAREST_TIES_TO_EVEN => Ok(FPRM::NearestTiesToEven),
        z3::DeclKind::FPA_RM_TOWARD_POSITIVE => Ok(FPRM::TowardPositive),
        z3::DeclKind::FPA_RM_TOWARD_NEGATIVE => Ok(FPRM::TowardNegative),
        z3::DeclKind::FPA_RM_TOWARD_ZERO => Ok(FPRM::TowardZero),
        z3::DeclKind::FPA_RM_NEAREST_TIES_TO_AWAY => Ok(FPRM::NearestTiesToAway),
        _ => Err(ClarirsError::ConversionError(
            "Unknown rounding mode".into(),
        )),
    }
}
