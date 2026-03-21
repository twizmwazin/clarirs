use crate::astext::child;
use clarirs_core::prelude::*;
use regex::Regex;
use z3::ast::{Ast, Dynamic};

use super::AstExtZ3;

fn decode_custom_unicode(input: &str) -> String {
    let re = Regex::new(r"\\u\{([0-9a-fA-F]+)\}").unwrap();
    re.replace_all(input, |caps: &regex::Captures| {
        let num = u32::from_str_radix(&caps[1], 16).unwrap();
        std::char::from_u32(num).unwrap().to_string()
    })
    .into_owned()
}

/// Convert a string to an integer using z3-sys (Z3_mk_str_to_int).
/// Not exposed by the z3 crate's String type.
pub(crate) fn str_to_int(s: &z3::ast::String) -> z3::ast::Int {
    let ctx = s.get_ctx();
    unsafe {
        z3::ast::Int::wrap(
            ctx,
            z3_sys::Z3_mk_str_to_int(ctx.get_z3_context(), s.get_z3_ast()).unwrap(),
        )
    }
}

/// Convert an integer to a string using z3-sys (Z3_mk_int_to_str).
fn int_to_str(i: &z3::ast::Int) -> z3::ast::String {
    let ctx = i.get_ctx();
    unsafe {
        z3::ast::String::wrap(
            ctx,
            z3_sys::Z3_mk_int_to_str(ctx.get_z3_context(), i.get_z3_ast()).unwrap(),
        )
    }
}

/// Find the index of a pattern in a string using z3-sys (Z3_mk_seq_index).
pub(crate) fn str_index_of_z3(
    haystack: &z3::ast::String,
    needle: &z3::ast::String,
    offset: &z3::ast::Int,
) -> z3::ast::Int {
    let ctx = haystack.get_ctx();
    unsafe {
        z3::ast::Int::wrap(
            ctx,
            z3_sys::Z3_mk_seq_index(
                ctx.get_z3_context(),
                haystack.get_z3_ast(),
                needle.get_z3_ast(),
                offset.get_z3_ast(),
            )
            .unwrap(),
        )
    }
}

/// Replace occurrences of a pattern in a string using z3-sys (Z3_mk_seq_replace).
pub(crate) fn str_replace_z3(
    s: &z3::ast::String,
    from: &z3::ast::String,
    to: &z3::ast::String,
) -> z3::ast::String {
    let ctx = s.get_ctx();
    unsafe {
        z3::ast::String::wrap(
            ctx,
            z3_sys::Z3_mk_seq_replace(
                ctx.get_z3_context(),
                s.get_z3_ast(),
                from.get_z3_ast(),
                to.get_z3_ast(),
            )
            .unwrap(),
        )
    }
}

pub(crate) fn to_z3(
    ast: &StringAst,
    children: &[Dynamic],
) -> Result<Dynamic, ClarirsError> {
    Ok(match ast.op() {
        StringOp::StringS(s) => {
            Dynamic::from(z3::ast::String::new_const(s.as_str()))
        }
        StringOp::StringV(s) => {
            Dynamic::from(z3::ast::String::from(s.as_str()))
        }
        StringOp::StrConcat(..) => {
            let a = child(children, 0)?.as_string().unwrap();
            let b = child(children, 1)?.as_string().unwrap();
            Dynamic::from(z3::ast::String::concat(&[a, b]))
        }
        StringOp::StrSubstr(..) => {
            let a = child(children, 0)?.as_string().unwrap();
            let offset_bv = child(children, 1)?.as_bv().unwrap();
            let offset_int = offset_bv.to_int(false);
            let len_bv = child(children, 2)?.as_bv().unwrap();
            let len_int = len_bv.to_int(false);
            Dynamic::from(a.substr(offset_int, len_int))
        }
        StringOp::StrReplace(..) => {
            let a = child(children, 0)?.as_string().unwrap();
            let b = child(children, 1)?.as_string().unwrap();
            let c = child(children, 2)?.as_string().unwrap();
            Dynamic::from(str_replace_z3(&a, &b, &c))
        }
        StringOp::BVToStr(_) => {
            let a = child(children, 0)?.as_bv().unwrap();
            let int_val = a.to_int(false);
            Dynamic::from(int_to_str(&int_val))
        }
        StringOp::ITE(..) => {
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
) -> Result<StringAst<'c>, ClarirsError> {
    let ast_kind = ast.kind();
    match ast_kind {
        z3::AstKind::App => {
            let decl = ast.safe_decl().map_err(|_| {
                ClarirsError::ConversionError("not an app".to_string())
            })?;
            let decl_kind = decl.kind();

            match decl_kind {
                z3::DeclKind::UNINTERPRETED => {
                    if ast.sort_kind() != z3::SortKind::Seq {
                        return Err(ClarirsError::ConversionError(
                            "expected a string".to_string(),
                        ));
                    }
                    // An uninterpreted constant of Seq sort with arity 0
                    // is a string symbol (variable)
                    let name = decl.name();
                    ctx.strings(&name)
                }
                z3::DeclKind::SEQ_CONCAT => {
                    let a = StringAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let b = StringAst::from_z3(ctx, ast.nth_child(1).unwrap())?;
                    ctx.str_concat(a, b)
                }
                z3::DeclKind::SEQ_EXTRACT => {
                    let a = StringAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let offset_int = ast.nth_child(1).unwrap();
                    let len_int = ast.nth_child(2).unwrap();

                    let offset_bv = z3::ast::BV::from_int(
                        &offset_int.as_int().unwrap(),
                        64,
                    );
                    let offset_simplified = Dynamic::from(offset_bv).simplify();
                    let offset = BitVecAst::from_z3(ctx, offset_simplified)?;

                    let len_bv = z3::ast::BV::from_int(
                        &len_int.as_int().unwrap(),
                        64,
                    );
                    let len_simplified = Dynamic::from(len_bv).simplify();
                    let len = BitVecAst::from_z3(ctx, len_simplified)?;

                    ctx.str_substr(a, offset, len)
                }
                z3::DeclKind::INT_TO_STR => {
                    let inner = ast.nth_child(0).unwrap();
                    let inner_decl = inner.safe_decl().map_err(|_| {
                        ClarirsError::ConversionError("not an app".to_string())
                    })?;
                    if inner_decl.kind() == z3::DeclKind::BV2INT {
                        let bv = BitVecAst::from_z3(ctx, inner.nth_child(0).unwrap())?;
                        ctx.bv_to_str(bv)
                    } else {
                        Err(ClarirsError::ConversionError(
                            "expected bv2int inside int_to_str".to_string(),
                        ))
                    }
                }
                z3::DeclKind::SEQ_REPLACE => {
                    let a = StringAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let b = StringAst::from_z3(ctx, ast.nth_child(1).unwrap())?;
                    let c = StringAst::from_z3(ctx, ast.nth_child(2).unwrap())?;
                    ctx.str_replace(a, b, c)
                }
                z3::DeclKind::ITE => {
                    let cond = BoolAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let then = StringAst::from_z3(ctx, ast.nth_child(1).unwrap())?;
                    let else_ = StringAst::from_z3(ctx, ast.nth_child(2).unwrap())?;
                    ctx.ite(cond, then, else_)
                }
                _ => {
                    // Check if it's a string constant
                    if let Some(s) = ast.as_string().and_then(|s| s.as_string()) {
                        let decoded_str = decode_custom_unicode(&s);
                        return ctx.stringv(decoded_str);
                    }
                    Err(ClarirsError::ConversionError(
                        format!("Failed converting from z3: unknown decl kind {:?} for string", decl_kind),
                    ))
                }
            }
        }
        _ => Err(ClarirsError::ConversionError(
            "Failed converting from z3: unknown ast kind for string".to_string(),
        )),
    }
}
