use crate::astext::{DynamicExt, child};
use clarirs_core::prelude::*;
use regex::Regex;
use std::sync::LazyLock;
use z3::ast::{Ast, Dynamic};

use super::AstExtZ3;

static UNICODE_RE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"\\u\{([0-9a-fA-F]+)\}").unwrap());

fn decode_custom_unicode(input: &str) -> String {
    UNICODE_RE
        .replace_all(input, |caps: &regex::Captures| {
            let num = u32::from_str_radix(&caps[1], 16).unwrap();
            std::char::from_u32(num).unwrap().to_string()
        })
        .into_owned()
}

/// Not exposed by the z3 crate's String type.
pub(crate) fn str_to_int(s: &z3::ast::String) -> z3::ast::Int {
    let ctx = s.get_ctx();
    unsafe {
        // z3-sys unwrap is safe: valid Z3 string AST
        z3::ast::Int::wrap(
            ctx,
            z3_sys::Z3_mk_str_to_int(ctx.get_z3_context(), s.get_z3_ast()).unwrap(),
        )
    }
}

fn int_to_str(i: &z3::ast::Int) -> z3::ast::String {
    let ctx = i.get_ctx();
    unsafe {
        // z3-sys unwrap is safe: valid Z3 int AST
        z3::ast::String::wrap(
            ctx,
            z3_sys::Z3_mk_int_to_str(ctx.get_z3_context(), i.get_z3_ast()).unwrap(),
        )
    }
}

pub(crate) fn str_index_of_z3(
    haystack: &z3::ast::String,
    needle: &z3::ast::String,
    offset: &z3::ast::Int,
) -> z3::ast::Int {
    let ctx = haystack.get_ctx();
    unsafe {
        // z3-sys unwrap is safe: valid Z3 ASTs
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

pub(crate) fn str_replace_z3(
    s: &z3::ast::String,
    from: &z3::ast::String,
    to: &z3::ast::String,
) -> z3::ast::String {
    let ctx = s.get_ctx();
    unsafe {
        // z3-sys unwrap is safe: valid Z3 ASTs
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

pub(crate) fn to_z3(ast: &StringAst, children: &[Dynamic]) -> Result<Dynamic, ClarirsError> {
    Ok(match ast.op() {
        StringOp::StringS(s) => Dynamic::from(z3::ast::String::new_const(s.as_str())),
        StringOp::StringV(s) => Dynamic::from(z3::ast::String::from(s.as_str())),
        StringOp::StrConcat(..) => Dynamic::from(z3::ast::String::concat(&[
            child(children, 0)?.to_string_ast()?,
            child(children, 1)?.to_string_ast()?,
        ])),
        StringOp::StrSubstr(..) => {
            let a = child(children, 0)?.to_string_ast()?;
            let offset_int = child(children, 1)?.to_bv()?.to_int(false);
            let len_int = child(children, 2)?.to_bv()?.to_int(false);
            Dynamic::from(a.substr(offset_int, len_int))
        }
        StringOp::StrReplace(..) => {
            let a = child(children, 0)?.to_string_ast()?;
            let b = child(children, 1)?.to_string_ast()?;
            let c = child(children, 2)?.to_string_ast()?;
            Dynamic::from(str_replace_z3(&a, &b, &c))
        }
        StringOp::BVToStr(_) => {
            let int_val = child(children, 0)?.to_bv()?.to_int(false);
            Dynamic::from(int_to_str(&int_val))
        }
        StringOp::ITE(..) => child(children, 0)?
            .to_bool()?
            .ite(child(children, 1)?, child(children, 2)?),
    })
}

pub(crate) fn from_z3<'c>(
    ctx: &'c Context<'c>,
    ast: Dynamic,
) -> Result<StringAst<'c>, ClarirsError> {
    let ast_kind = ast.kind();
    match ast_kind {
        z3::AstKind::App => {
            let decl = ast.get_decl()?;
            let decl_kind = decl.kind();

            match decl_kind {
                z3::DeclKind::UNINTERPRETED => {
                    if ast.sort_kind() != z3::SortKind::Seq {
                        return Err(ClarirsError::ConversionError("expected a string".into()));
                    }
                    ctx.strings(decl.name())
                }
                z3::DeclKind::SEQ_CONCAT => {
                    let a = StringAst::from_z3(ctx, ast.nth(0)?)?;
                    let b = StringAst::from_z3(ctx, ast.nth(1)?)?;
                    ctx.str_concat(a, b)
                }
                z3::DeclKind::SEQ_EXTRACT => {
                    let a = StringAst::from_z3(ctx, ast.nth(0)?)?;
                    let offset_int = ast.nth(1)?;
                    let len_int = ast.nth(2)?;

                    let offset_bv = z3::ast::BV::from_int(&offset_int.to_int()?, 64);
                    let offset_simplified = Dynamic::from(offset_bv).simplify();
                    let offset = BitVecAst::from_z3(ctx, offset_simplified)?;

                    let len_bv = z3::ast::BV::from_int(&len_int.to_int()?, 64);
                    let len_simplified = Dynamic::from(len_bv).simplify();
                    let len = BitVecAst::from_z3(ctx, len_simplified)?;

                    ctx.str_substr(a, offset, len)
                }
                z3::DeclKind::INT_TO_STR => {
                    let inner = ast.nth(0)?;
                    let inner_decl = inner.get_decl()?;
                    if inner_decl.kind() == z3::DeclKind::BV2INT {
                        let bv = BitVecAst::from_z3(ctx, inner.nth(0)?)?;
                        ctx.bv_to_str(bv)
                    } else {
                        Err(ClarirsError::ConversionError(
                            "expected bv2int inside int_to_str".into(),
                        ))
                    }
                }
                z3::DeclKind::SEQ_REPLACE => {
                    let a = StringAst::from_z3(ctx, ast.nth(0)?)?;
                    let b = StringAst::from_z3(ctx, ast.nth(1)?)?;
                    let c = StringAst::from_z3(ctx, ast.nth(2)?)?;
                    ctx.str_replace(a, b, c)
                }
                z3::DeclKind::ITE => {
                    let cond = BoolAst::from_z3(ctx, ast.nth(0)?)?;
                    let then = StringAst::from_z3(ctx, ast.nth(1)?)?;
                    let else_ = StringAst::from_z3(ctx, ast.nth(2)?)?;
                    ctx.ite(cond, then, else_)
                }
                _ => {
                    // Check if it's a string constant
                    if let Some(s) = ast.as_string().and_then(|s| s.as_string()) {
                        let decoded_str = decode_custom_unicode(&s);
                        return ctx.stringv(decoded_str);
                    }
                    Err(ClarirsError::ConversionError(format!(
                        "Failed converting from z3: unknown decl kind {decl_kind:?} for string",
                    )))
                }
            }
        }
        _ => Err(ClarirsError::ConversionError(
            "Failed converting from z3: unknown ast kind for string".into(),
        )),
    }
}
