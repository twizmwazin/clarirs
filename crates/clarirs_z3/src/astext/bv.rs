use clarirs_core::{ast::bitvec::BitVecOpExt, prelude::*};
use num_bigint::BigUint;
use num_traits::Num;
use z3::ast::{Ast, Dynamic};

use super::AstExtZ3;
use crate::astext::child;

/// Helper to get an integer parameter from a Z3 func_decl.
/// This is the only place we need z3-sys directly, as the z3 crate
/// does not expose func_decl parameters.
fn get_decl_int_parameter(ast: &Dynamic, param_index: u32) -> u32 {
    let ctx = ast.get_ctx();
    unsafe {
        let z3_ctx = ctx.get_z3_context();
        let app = z3_sys::Z3_to_app(z3_ctx, ast.get_z3_ast()).unwrap();
        let decl = z3_sys::Z3_get_app_decl(z3_ctx, app).unwrap();
        z3_sys::Z3_get_decl_int_parameter(z3_ctx, decl, param_index) as u32
    }
}

/// Fold a binary BV operation across all children.
fn fold_bv(children: &[Dynamic], op: fn(&z3::ast::BV, &z3::ast::BV) -> z3::ast::BV) -> Dynamic {
    let mut result = children[0].as_bv().unwrap();
    for c in &children[1..] {
        result = op(&result, &c.as_bv().unwrap());
    }
    Dynamic::from(result)
}

/// Apply a binary BV operation to two children.
fn binop_bv(children: &[Dynamic], op: fn(&z3::ast::BV, &z3::ast::BV) -> z3::ast::BV) -> Dynamic {
    Dynamic::from(op(
        &children[0].as_bv().unwrap(),
        &children[1].as_bv().unwrap(),
    ))
}

pub(crate) fn to_z3(ast: &BitVecAst, children: &[Dynamic]) -> Result<Dynamic, ClarirsError> {
    Ok(match ast.op() {
        BitVecOp::BVS(s, w) => Dynamic::from(z3::ast::BV::new_const(s.as_str(), *w)),
        BitVecOp::BVV(v) => {
            let biguint = v.to_biguint();
            if let Ok(val) = u64::try_from(&biguint) {
                Dynamic::from(z3::ast::BV::from_u64(val, v.len()))
            } else {
                let int_ast = z3::ast::Int::from_big_int(&num_bigint::BigInt::from(biguint));
                Dynamic::from(z3::ast::BV::from_int(&int_ast, v.len()))
            }
        }
        BitVecOp::Not(..) => Dynamic::from(child(children, 0)?.as_bv().unwrap().bvnot()),
        BitVecOp::Neg(..) => Dynamic::from(child(children, 0)?.as_bv().unwrap().bvneg()),
        BitVecOp::And(..) => fold_bv(children, z3::ast::BV::bvand),
        BitVecOp::Or(..) => fold_bv(children, z3::ast::BV::bvor),
        BitVecOp::Xor(..) => fold_bv(children, z3::ast::BV::bvxor),
        BitVecOp::Add(..) => fold_bv(children, z3::ast::BV::bvadd),
        BitVecOp::Sub(..) => binop_bv(children, z3::ast::BV::bvsub),
        BitVecOp::Mul(..) => fold_bv(children, z3::ast::BV::bvmul),
        BitVecOp::UDiv(..) => binop_bv(children, z3::ast::BV::bvudiv),
        BitVecOp::SDiv(..) => binop_bv(children, z3::ast::BV::bvsdiv),
        BitVecOp::URem(..) => binop_bv(children, z3::ast::BV::bvurem),
        BitVecOp::SRem(..) => binop_bv(children, z3::ast::BV::bvsrem),
        BitVecOp::ShL(..) => binop_bv(children, z3::ast::BV::bvshl),
        BitVecOp::LShR(..) => binop_bv(children, z3::ast::BV::bvlshr),
        BitVecOp::AShR(..) => binop_bv(children, z3::ast::BV::bvashr),
        BitVecOp::RotateLeft(..) => binop_bv(children, z3::ast::BV::bvrotl),
        BitVecOp::RotateRight(..) => binop_bv(children, z3::ast::BV::bvrotr),
        BitVecOp::ZeroExt(_, i) => {
            let a = child(children, 0)?.as_bv().unwrap();
            Dynamic::from(a.zero_ext(*i))
        }
        BitVecOp::SignExt(_, i) => {
            let a = child(children, 0)?.as_bv().unwrap();
            Dynamic::from(a.sign_ext(*i))
        }
        BitVecOp::Extract(a, high, low) => {
            if high >= &a.size() {
                return Err(ClarirsError::ConversionError(
                    "high index is greater than bitvector size".to_string(),
                ));
            }
            if low >= &a.size() {
                return Err(ClarirsError::ConversionError(
                    "low index is greater than bitvector size".to_string(),
                ));
            }
            if low > high {
                return Err(ClarirsError::ConversionError(
                    "low index is greater than high index".to_string(),
                ));
            }
            let a = child(children, 0)?.as_bv().unwrap();
            Dynamic::from(a.extract(*high, *low))
        }
        BitVecOp::Concat(args) => {
            if args.is_empty() {
                return Err(ClarirsError::InvalidArguments(
                    "Concat requires at least one argument".to_string(),
                ));
            }
            let mut result = child(children, 0)?.as_bv().unwrap();
            for i in 1..children.len() {
                result = result.concat(&child(children, i)?.as_bv().unwrap());
            }
            Dynamic::from(result)
        }
        BitVecOp::ByteReverse(a) => {
            let size = a.size();
            if size == 0 || size % 8 != 0 {
                return Err(ClarirsError::ConversionError(
                    "reverse only supports bitvectors with size multiple of 8".to_string(),
                ));
            }

            let child_z3 = child(children, 0)?.as_bv().unwrap();
            let num_bytes = size / 8;

            let mut result = child_z3.extract(7, 0);
            for i in 1..num_bytes {
                let high = (i + 1) * 8 - 1;
                let low = i * 8;
                let byte = child_z3.extract(high, low);
                result = result.concat(&byte);
            }
            Dynamic::from(result)
        }
        BitVecOp::ITE(..) => {
            let cond = child(children, 0)?.as_bool().unwrap();
            let then = child(children, 1)?;
            let else_ = child(children, 2)?;
            cond.ite(then, else_)
        }
        BitVecOp::FpToIEEEBV(..) => {
            let a = child(children, 0)?.as_float().unwrap();
            Dynamic::from(a.to_ieee_bv())
        }
        BitVecOp::FpToUBV(_, size, rm) => {
            let rm_ast = super::float::fprm_to_z3(*rm)?;
            let a = child(children, 0)?.as_float().unwrap();
            Dynamic::from(a.to_ubv_with_rounding_mode(&rm_ast, *size))
        }
        BitVecOp::FpToSBV(_, size, rm) => {
            let rm_ast = super::float::fprm_to_z3(*rm)?;
            let a = child(children, 0)?.as_float().unwrap();
            Dynamic::from(a.to_sbv_with_rounding_mode(&rm_ast, *size))
        }
        BitVecOp::StrLen(..) => {
            let a = child(children, 0)?.as_string().unwrap();
            let str_len = a.length();
            Dynamic::from(z3::ast::BV::from_int(&str_len, 64))
        }
        BitVecOp::StrIndexOf(..) => {
            let haystack = child(children, 0)?.as_string().unwrap();
            let needle = child(children, 1)?.as_string().unwrap();
            let offset_bv = child(children, 2)?.as_bv().unwrap();
            let offset_int = offset_bv.to_int(false);
            let index_int = super::string::str_index_of_z3(&haystack, &needle, &offset_int);
            Dynamic::from(z3::ast::BV::from_int(&index_int, 64))
        }
        BitVecOp::StrToBV(..) => {
            let a = child(children, 0)?.as_string().unwrap();
            let int_val = super::string::str_to_int(&a);
            Dynamic::from(z3::ast::BV::from_int(&int_val, 64))
        }
        BitVecOp::Union(..) | BitVecOp::Intersection(..) | BitVecOp::Widen(..) => {
            return Err(ClarirsError::ConversionError(
                "vsa types are not currently supported in the z3 backend".to_string(),
            ));
        }
    })
}

pub(crate) fn from_z3<'c>(
    ctx: &'c Context<'c>,
    ast: Dynamic,
) -> Result<BitVecAst<'c>, ClarirsError> {
    let ast_kind = ast.kind();
    match ast_kind {
        z3::AstKind::Numeral => {
            let bv = ast.as_bv().ok_or_else(|| {
                ClarirsError::ConversionError("expected a bv numeral".to_string())
            })?;
            let sort_num = bv.get_size();
            let numeral_str = format!("{ast}");
            // Z3 may format as #x... or #b... or decimal
            let biguint = if let Some(hex) = numeral_str.strip_prefix("#x") {
                let val = BigUint::from_str_radix(hex, 16).map_err(|_| {
                    ClarirsError::ConversionError(format!("failed to parse hex bv: {numeral_str}"))
                })?;
                BitVec::from_biguint(&val, sort_num).map_err(|e| {
                    ClarirsError::ConversionError(format!("failed to create bv: {e:?}"))
                })?
            } else if let Some(bin) = numeral_str.strip_prefix("#b") {
                let val = BigUint::from_str_radix(bin, 2).map_err(|_| {
                    ClarirsError::ConversionError(format!("failed to parse bin bv: {numeral_str}"))
                })?;
                BitVec::from_biguint(&val, sort_num).map_err(|e| {
                    ClarirsError::ConversionError(format!("failed to create bv: {e:?}"))
                })?
            } else {
                BitVec::from_str(&numeral_str, sort_num).map_err(|e| {
                    ClarirsError::ConversionError(format!(
                        "failed to parse bv numeral: {numeral_str}: {e:?}"
                    ))
                })?
            };
            ctx.bvv(biguint)
        }
        z3::AstKind::App => {
            let decl = ast
                .safe_decl()
                .map_err(|_| ClarirsError::ConversionError("not an app".to_string()))?;
            let decl_kind = decl.kind();
            let bv = ast
                .as_bv()
                .ok_or_else(|| ClarirsError::ConversionError("expected bv sort".to_string()))?;
            let width = bv.get_size();

            match decl_kind {
                z3::DeclKind::UNINTERPRETED => {
                    let name = decl.name();
                    ctx.bvs(&name, width)
                }
                z3::DeclKind::BNOT => {
                    let inner = BitVecAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    ctx.not(inner)
                }
                z3::DeclKind::BNEG => {
                    let inner = BitVecAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    ctx.neg(inner)
                }
                z3::DeclKind::BAND
                | z3::DeclKind::BOR
                | z3::DeclKind::BXOR
                | z3::DeclKind::BADD
                | z3::DeclKind::BMUL => {
                    let num_args = ast.num_children();
                    let mut args = Vec::with_capacity(num_args);
                    for i in 0..num_args {
                        args.push(BitVecAst::from_z3(ctx, ast.nth_child(i).unwrap())?);
                    }
                    match decl_kind {
                        z3::DeclKind::BAND => ctx.bv_and_many(args),
                        z3::DeclKind::BOR => ctx.bv_or_many(args),
                        z3::DeclKind::BXOR => ctx.bv_xor_many(args),
                        z3::DeclKind::BADD => ctx.add_many(args),
                        z3::DeclKind::BMUL => ctx.mul_many(args),
                        _ => unreachable!(),
                    }
                }
                z3::DeclKind::BSUB
                | z3::DeclKind::BUDIV
                | z3::DeclKind::BSDIV
                | z3::DeclKind::BUREM
                | z3::DeclKind::BSREM
                | z3::DeclKind::BSHL
                | z3::DeclKind::BLSHR
                | z3::DeclKind::BASHR => {
                    let a = BitVecAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let b = BitVecAst::from_z3(ctx, ast.nth_child(1).unwrap())?;
                    match decl_kind {
                        z3::DeclKind::BSUB => ctx.sub(a, b),
                        z3::DeclKind::BUDIV => ctx.udiv(a, b),
                        z3::DeclKind::BSDIV => ctx.sdiv(a, b),
                        z3::DeclKind::BUREM => ctx.urem(a, b),
                        z3::DeclKind::BSREM => ctx.srem(a, b),
                        z3::DeclKind::BSHL => ctx.shl(a, b),
                        z3::DeclKind::BLSHR => ctx.lshr(a, b),
                        z3::DeclKind::BASHR => ctx.ashr(a, b),
                        _ => unreachable!(),
                    }
                }
                z3::DeclKind::EXT_ROTATE_LEFT | z3::DeclKind::EXT_ROTATE_RIGHT => {
                    let a = BitVecAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let b = BitVecAst::from_z3(ctx, ast.nth_child(1).unwrap())?;
                    match decl_kind {
                        z3::DeclKind::EXT_ROTATE_LEFT => ctx.rotate_left(a, b),
                        z3::DeclKind::EXT_ROTATE_RIGHT => ctx.rotate_right(a, b),
                        _ => unreachable!(),
                    }
                }
                z3::DeclKind::ZERO_EXT | z3::DeclKind::SIGN_EXT => {
                    let inner = BitVecAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let i = get_decl_int_parameter(&ast, 0);
                    match decl_kind {
                        z3::DeclKind::ZERO_EXT => ctx.zero_ext(&inner, i),
                        z3::DeclKind::SIGN_EXT => ctx.sign_ext(inner, i),
                        _ => unreachable!(),
                    }
                }
                z3::DeclKind::EXTRACT => {
                    let inner = BitVecAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let high = get_decl_int_parameter(&ast, 0);
                    let low = get_decl_int_parameter(&ast, 1);
                    ctx.extract(inner, high, low)
                }
                z3::DeclKind::CONCAT => {
                    let num_args = ast.num_children();
                    let mut concat_args = Vec::with_capacity(num_args);
                    for i in 0..num_args {
                        concat_args.push(BitVecAst::from_z3(ctx, ast.nth_child(i).unwrap())?);
                    }
                    ctx.concat(concat_args)
                }
                z3::DeclKind::ITE => {
                    let cond = BoolAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let then = BitVecAst::from_z3(ctx, ast.nth_child(1).unwrap())?;
                    let else_ = BitVecAst::from_z3(ctx, ast.nth_child(2).unwrap())?;
                    ctx.ite(cond, then, else_)
                }
                z3::DeclKind::INT2BV => {
                    let inner_int = ast.nth_child(0).unwrap();
                    let inner_ast_kind = inner_int.kind();
                    match inner_ast_kind {
                        z3::AstKind::Numeral => {
                            let numeral_str = format!("{inner_int}");
                            let biguint = BitVec::from_str(&numeral_str, width).map_err(|e| {
                                ClarirsError::ConversionError(format!(
                                    "failed to parse int2bv numeral: {numeral_str}: {e:?}"
                                ))
                            })?;
                            ctx.bvv(biguint)
                        }
                        z3::AstKind::App => {
                            let inner_decl = inner_int.safe_decl().map_err(|_| {
                                ClarirsError::ConversionError("not an app".to_string())
                            })?;
                            let inner_kind = inner_decl.kind();

                            match inner_kind {
                                z3::DeclKind::BV2INT => {
                                    BitVecAst::from_z3(ctx, inner_int.nth_child(0).unwrap())
                                }
                                z3::DeclKind::SEQ_INDEX => {
                                    let haystack =
                                        StringAst::from_z3(ctx, inner_int.nth_child(0).unwrap())?;
                                    let needle =
                                        StringAst::from_z3(ctx, inner_int.nth_child(1).unwrap())?;
                                    let offset_arg = inner_int.nth_child(2).unwrap();
                                    let offset_bv_dyn =
                                        z3::ast::BV::from_int(&offset_arg.as_int().unwrap(), 64);
                                    let offset_simplified = Dynamic::from(offset_bv_dyn).simplify();
                                    let offset = BitVecAst::from_z3(ctx, offset_simplified)?;
                                    ctx.str_index_of(haystack, needle, offset)
                                }
                                z3::DeclKind::STR_TO_INT => {
                                    let s =
                                        StringAst::from_z3(ctx, inner_int.nth_child(0).unwrap())?;
                                    ctx.str_to_bv(s)
                                }
                                z3::DeclKind::SEQ_LENGTH => {
                                    let s =
                                        StringAst::from_z3(ctx, inner_int.nth_child(0).unwrap())?;
                                    ctx.str_len(s)
                                }
                                _ => Err(ClarirsError::ConversionError(format!(
                                    "unexpected inner decl kind in Int2bv: {:?}",
                                    inner_kind,
                                ))),
                            }
                        }
                        _ => Err(ClarirsError::ConversionError(
                            "expected a numeral or bv2int".to_string(),
                        )),
                    }
                }
                _ => Err(ClarirsError::ConversionError(
                    "Failed converting from z3: unknown decl kind for bitvec".to_string(),
                )),
            }
        }
        _ => Err(ClarirsError::ConversionError(
            "Failed converting from z3: unknown ast kind for bitvec".to_string(),
        )),
    }
}
