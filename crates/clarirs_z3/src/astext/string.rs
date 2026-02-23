use crate::{astext::child, check_z3_error, rc::RcAst, Z3_CONTEXT};
use clarirs_core::prelude::*;
use clarirs_z3_sys::{self as z3};
use regex::Regex;

use super::AstExtZ3;

fn mk_bv2int(bv: &RcAst) -> Result<RcAst, ClarirsError> {
    Z3_CONTEXT.with(|&z3_ctx| unsafe { RcAst::try_from(z3::mk_bv2int(z3_ctx, **bv, false)) })
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
                let sym = z3::mk_string_symbol(z3_ctx, s_cstr.as_ptr());
                let sort = z3::mk_seq_sort(z3_ctx, z3::mk_char_sort(z3_ctx));
                RcAst::try_from(z3::mk_const(z3_ctx, sym, sort))?
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
                RcAst::try_from(z3::mk_string(z3_ctx, cstr.as_ptr()))?
            }
            StringOp::StrConcat(..) => {
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                RcAst::try_from(z3::mk_seq_concat(z3_ctx, 2, [**a, **b].as_ptr()))?
            }
            StringOp::StrSubstr(..) => {
                let a = child(children, 0)?;
                let offset_bv = child(children, 1)?;
                let offset_int = mk_bv2int(offset_bv)?;
                let len_bv = child(children, 2)?;
                let len_int = mk_bv2int(len_bv)?;
                RcAst::try_from(z3::mk_seq_extract(z3_ctx, **a, *offset_int, *len_int))?
            }
            StringOp::StrReplace(..) => {
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                let c = child(children, 2)?;
                RcAst::try_from(z3::mk_seq_replace(z3_ctx, **a, **b, **c))?
            }
            StringOp::BVToStr(_) => todo!("BVToStr - no direct Z3 equivalent"),
            StringOp::ITE(cond, then, else_) => {
                let cond = cond.to_z3()?;
                let then = then.to_z3()?;
                let else_ = else_.to_z3()?;
                RcAst::try_from(z3::mk_ite(z3_ctx, *cond, *then, *else_))?
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
        let ast_kind = z3::get_ast_kind(z3_ctx, *ast);
        match ast_kind {
            z3::AstKind::App => {
                let app = z3::to_app(z3_ctx, *ast);
                let decl = z3::get_app_decl(z3_ctx, app);
                let decl_kind = z3::get_decl_kind(z3_ctx, decl);

                match decl_kind {
                    // Handle string constants
                    _ if z3::is_string(z3_ctx, *ast) => {
                        let string_ptr = z3::get_string(z3_ctx, *ast);
                        let raw_str = std::ffi::CStr::from_ptr(string_ptr).to_str().unwrap();
                        let decoded_str = decode_custom_unicode(raw_str);
                        ctx.stringv(decoded_str)
                    }
                    z3::DeclKind::Uninterpreted => {
                        // Verify it's a string
                        let sort = z3::get_sort(z3_ctx, *ast);
                        let sort_kind = z3::get_sort_kind(z3_ctx, sort);
                        if sort_kind != z3::SortKind::Seq {
                            return Err(ClarirsError::ConversionError(
                                "expected a string".to_string(),
                            ));
                        }
                        let sym = z3::get_decl_name(z3_ctx, decl);
                        let name = z3::get_symbol_string(z3_ctx, sym);
                        let name = std::ffi::CStr::from_ptr(name).to_str().unwrap();
                        ctx.strings(name)
                    }
                    z3::DeclKind::SeqConcat => {
                        let arg0 = RcAst::try_from(z3::get_app_arg(z3_ctx, app, 0))?;
                        let arg1 = RcAst::try_from(z3::get_app_arg(z3_ctx, app, 1))?;
                        let a = StringAst::from_z3(ctx, arg0)?;
                        let b = StringAst::from_z3(ctx, arg1)?;
                        ctx.str_concat(a, b)
                    }
                    z3::DeclKind::SeqExtract => {
                        let arg0 = RcAst::try_from(z3::get_app_arg(z3_ctx, app, 0))?;
                        let arg1 = RcAst::try_from(z3::get_app_arg(z3_ctx, app, 1))?;
                        let arg2 = RcAst::try_from(z3::get_app_arg(z3_ctx, app, 2))?;
                        let a = StringAst::from_z3(ctx, arg0)?;

                        let offset_bv = RcAst::try_from(z3::mk_int2bv(z3_ctx, 64, *arg1))?;
                        let offset_simplified = RcAst::try_from(z3::simplify(z3_ctx, *offset_bv))?;
                        let offset = BitVecAst::from_z3(ctx, offset_simplified)?;

                        let len_bv = RcAst::try_from(z3::mk_int2bv(z3_ctx, 64, *arg2))?;
                        let len_simplified = RcAst::try_from(z3::simplify(z3_ctx, *len_bv))?;
                        let len = BitVecAst::from_z3(ctx, len_simplified)?;

                        ctx.str_substr(a, offset, len)
                    }
                    z3::DeclKind::SeqReplace => {
                        let arg0 = RcAst::try_from(z3::get_app_arg(z3_ctx, app, 0))?;
                        let arg1 = RcAst::try_from(z3::get_app_arg(z3_ctx, app, 1))?;
                        let arg2 = RcAst::try_from(z3::get_app_arg(z3_ctx, app, 2))?;
                        let a = StringAst::from_z3(ctx, arg0)?;
                        let b = StringAst::from_z3(ctx, arg1)?;
                        let c = StringAst::from_z3(ctx, arg2)?;
                        ctx.str_replace(a, b, c)
                    }
                    z3::DeclKind::Ite => {
                        let cond = RcAst::try_from(z3::get_app_arg(z3_ctx, app, 0))?;
                        let then = RcAst::try_from(z3::get_app_arg(z3_ctx, app, 1))?;
                        let else_ = RcAst::try_from(z3::get_app_arg(z3_ctx, app, 2))?;
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
