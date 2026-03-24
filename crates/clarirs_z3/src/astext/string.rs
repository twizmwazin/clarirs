use crate::{Z3_CONTEXT, astext::child, check_z3_error, rc::RcAst};
use clarirs_core::prelude::*;
use regex::Regex;

use super::AstExtZ3;

fn mk_bv2int(bv: &RcAst) -> Result<RcAst, ClarirsError> {
    Z3_CONTEXT.with(|&z3_ctx| unsafe { RcAst::try_from(z3_sys::Z3_mk_bv2int(z3_ctx, **bv, false).expect("Z3_mk_bv2int returned null")) })
}

fn decode_custom_unicode(input: &str) -> String {
    // Compile the regex pattern that matches "\u{...}"
    let re = Regex::new(r"\\u\{([0-9a-fA-F]+)\}").unwrap();

    // Replace all matches with the corresponding Unicode character.
    re.replace_all(input, |caps: &regex::Captures| {
        // Extract the hexadecimal part from the capture group.
        let num = u32::from_str_radix(&caps[1], 16).unwrap();
        // Convert the number to a Unicode character and then to a String.
        std::char::from_u32(num).unwrap().to_string()
    })
    .into_owned()
}

pub(crate) fn to_z3(ast: &StringAst, children: &[RcAst]) -> Result<RcAst, ClarirsError> {
    Z3_CONTEXT.with(|&z3_ctx| unsafe {
        Ok(match ast.op() {
            StringOp::StringS(s) => {
                let s_cstr = std::ffi::CString::new(s.as_str()).unwrap();
                let sym = z3_sys::Z3_mk_string_symbol(z3_ctx, s_cstr.as_ptr()).expect("Z3_mk_string_symbol returned null");
                let sort = z3_sys::Z3_mk_string_sort(z3_ctx).expect("Z3_mk_string_sort returned null");
                RcAst::try_from(z3_sys::Z3_mk_const(z3_ctx, sym, sort).expect("Z3_mk_const returned null"))?
            }
            StringOp::StringV(s) => {
                let mut encoded = String::new();
                for ch in s.chars() {
                    if ch.is_ascii() {
                        encoded.push(ch);
                    } else {
                        let escape = format!("\\u{{{:04X}}}", ch as u32);
                        encoded.push_str(&escape);
                    }
                }
                let cstr = std::ffi::CString::new(encoded).unwrap();
                RcAst::try_from(z3_sys::Z3_mk_string(z3_ctx, cstr.as_ptr()).expect("Z3_mk_string returned null"))?
            }
            StringOp::StrConcat(..) => {
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                RcAst::try_from(z3_sys::Z3_mk_seq_concat(z3_ctx, 2, [**a, **b].as_ptr()).expect("Z3_mk_seq_concat returned null"))?
            }
            StringOp::StrSubstr(..) => {
                let a = child(children, 0)?;
                let offset_bv = child(children, 1)?;
                let offset_int = mk_bv2int(offset_bv)?;
                let len_bv = child(children, 2)?;
                let len_int = mk_bv2int(len_bv)?;
                RcAst::try_from(z3_sys::Z3_mk_seq_extract(z3_ctx, **a, *offset_int, *len_int).expect("Z3_mk_seq_extract returned null"))?
            }
            StringOp::StrReplace(..) => {
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                let c = child(children, 2)?;
                RcAst::try_from(z3_sys::Z3_mk_seq_replace(z3_ctx, **a, **b, **c).expect("Z3_mk_seq_replace returned null"))?
            }
            StringOp::BVToStr(_) => {
                let a = child(children, 0)?;
                let int_val = mk_bv2int(a)?;
                RcAst::try_from(z3_sys::Z3_mk_int_to_str(z3_ctx, *int_val).expect("Z3_mk_int_to_str returned null"))?
            }
            StringOp::ITE(..) => {
                let cond = child(children, 0)?;
                let then = child(children, 1)?;
                let else_ = child(children, 2)?;
                RcAst::try_from(z3_sys::Z3_mk_ite(z3_ctx, **cond, **then, **else_).expect("Z3_mk_ite returned null"))?
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
) -> Result<StringAst<'c>, ClarirsError> {
    Z3_CONTEXT.with(|&z3_ctx| unsafe {
        let ast = ast.into();
        let ast_kind = z3_sys::Z3_get_ast_kind(z3_ctx, *ast);
        match ast_kind {
            z3_sys::AstKind::App => {
                let app = z3_sys::Z3_to_app(z3_ctx, *ast).expect("Z3_to_app returned null");
                let decl = z3_sys::Z3_get_app_decl(z3_ctx, app).expect("Z3_get_app_decl returned null");
                let decl_kind = z3_sys::Z3_get_decl_kind(z3_ctx, decl);

                match decl_kind {
                    // Handle string constants
                    _ if z3_sys::Z3_is_string(z3_ctx, *ast) => {
                        let string_ptr = z3_sys::Z3_get_string(z3_ctx, *ast);
                        let raw_str = std::ffi::CStr::from_ptr(string_ptr).to_str().unwrap();
                        let decoded_str = decode_custom_unicode(raw_str);
                        ctx.stringv(decoded_str)
                    }
                    z3_sys::DeclKind::UNINTERPRETED => {
                        // Verify it's a string
                        let sort = z3_sys::Z3_get_sort(z3_ctx, *ast).expect("Z3_get_sort returned null");
                        let sort_kind = z3_sys::Z3_get_sort_kind(z3_ctx, sort);
                        if sort_kind != z3_sys::SortKind::Seq {
                            return Err(ClarirsError::ConversionError(
                                "expected a string".to_string(),
                            ));
                        }
                        let sym = z3_sys::Z3_get_decl_name(z3_ctx, decl).expect("Z3_get_decl_name returned null");
                        let name = z3_sys::Z3_get_symbol_string(z3_ctx, sym);
                        let name = std::ffi::CStr::from_ptr(name).to_str().unwrap();
                        ctx.strings(name)
                    }
                    z3_sys::DeclKind::SEQ_CONCAT => {
                        let arg0 = RcAst::try_from(z3_sys::Z3_get_app_arg(z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let arg1 = RcAst::try_from(z3_sys::Z3_get_app_arg(z3_ctx, app, 1).expect("Z3_get_app_arg returned null"))?;
                        let a = StringAst::from_z3(ctx, arg0)?;
                        let b = StringAst::from_z3(ctx, arg1)?;
                        ctx.str_concat(a, b)
                    }
                    z3_sys::DeclKind::SEQ_EXTRACT => {
                        let arg0 = RcAst::try_from(z3_sys::Z3_get_app_arg(z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let arg1 = RcAst::try_from(z3_sys::Z3_get_app_arg(z3_ctx, app, 1).expect("Z3_get_app_arg returned null"))?;
                        let arg2 = RcAst::try_from(z3_sys::Z3_get_app_arg(z3_ctx, app, 2).expect("Z3_get_app_arg returned null"))?;
                        let a = StringAst::from_z3(ctx, arg0)?;

                        let offset_bv = RcAst::try_from(z3_sys::Z3_mk_int2bv(z3_ctx, 64, *arg1).expect("Z3_mk_int2bv returned null"))?;
                        let offset_simplified = RcAst::try_from(z3_sys::Z3_simplify(z3_ctx, *offset_bv).expect("Z3_simplify returned null"))?;
                        let offset = BitVecAst::from_z3(ctx, offset_simplified)?;

                        let len_bv = RcAst::try_from(z3_sys::Z3_mk_int2bv(z3_ctx, 64, *arg2).expect("Z3_mk_int2bv returned null"))?;
                        let len_simplified = RcAst::try_from(z3_sys::Z3_simplify(z3_ctx, *len_bv).expect("Z3_simplify returned null"))?;
                        let len = BitVecAst::from_z3(ctx, len_simplified)?;

                        ctx.str_substr(a, offset, len)
                    }
                    z3_sys::DeclKind::INT_TO_STR => {
                        // int.to.str(bv2int(bv)) -> BVToStr(bv)
                        let arg0 = RcAst::try_from(z3_sys::Z3_get_app_arg(z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let inner_app = z3_sys::Z3_to_app(z3_ctx, *arg0).expect("Z3_to_app returned null");
                        let inner_decl = z3_sys::Z3_get_app_decl(z3_ctx, inner_app).expect("Z3_get_app_decl returned null");
                        let inner_kind = z3_sys::Z3_get_decl_kind(z3_ctx, inner_decl);
                        if inner_kind == z3_sys::DeclKind::BV2INT {
                            let bv_arg = RcAst::try_from(z3_sys::Z3_get_app_arg(z3_ctx, inner_app, 0).expect("Z3_get_app_arg returned null"))?;
                            let bv = BitVecAst::from_z3(ctx, bv_arg)?;
                            ctx.bv_to_str(bv)
                        } else {
                            Err(ClarirsError::ConversionError(
                                "expected bv2int inside int_to_str".to_string(),
                            ))
                        }
                    }
                    z3_sys::DeclKind::SEQ_REPLACE => {
                        let arg0 = RcAst::try_from(z3_sys::Z3_get_app_arg(z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let arg1 = RcAst::try_from(z3_sys::Z3_get_app_arg(z3_ctx, app, 1).expect("Z3_get_app_arg returned null"))?;
                        let arg2 = RcAst::try_from(z3_sys::Z3_get_app_arg(z3_ctx, app, 2).expect("Z3_get_app_arg returned null"))?;
                        let a = StringAst::from_z3(ctx, arg0)?;
                        let b = StringAst::from_z3(ctx, arg1)?;
                        let c = StringAst::from_z3(ctx, arg2)?;
                        ctx.str_replace(a, b, c)
                    }
                    z3_sys::DeclKind::ITE => {
                        let cond = RcAst::try_from(z3_sys::Z3_get_app_arg(z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let then = RcAst::try_from(z3_sys::Z3_get_app_arg(z3_ctx, app, 1).expect("Z3_get_app_arg returned null"))?;
                        let else_ = RcAst::try_from(z3_sys::Z3_get_app_arg(z3_ctx, app, 2).expect("Z3_get_app_arg returned null"))?;
                        let cond = BoolAst::from_z3(ctx, cond)?;
                        let then = StringAst::from_z3(ctx, then)?;
                        let else_ = StringAst::from_z3(ctx, else_)?;
                        ctx.ite(cond, then, else_)
                    }
                    _ => Err(ClarirsError::ConversionError(
                        "Failed converting from z3: unknown decl kind for string".to_string(),
                    )),
                }
            }
            _ => Err(ClarirsError::ConversionError(
                "Failed converting from z3: unknown ast kind for string".to_string(),
            )),
        }
    })
}
