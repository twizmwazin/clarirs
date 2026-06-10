use super::{extract_bitvec_child, extract_bool_child, extract_string_child};
use crate::prelude::*;

pub(crate) fn excavate_ite<'c>(
    ast: &AstRef<'c>,
    children: &[AstRef<'c>],
) -> Result<AstRef<'c>, ClarirsError> {
    let ctx = ast.context();

    match ast.op() {
        AstOp::StringS(..) | AstOp::StringV(..) => Ok(ast.clone()),
        AstOp::StrConcat(..) => {
            let lhs = extract_string_child(children, 0)?;
            let rhs = extract_string_child(children, 1)?;

            if let AstOp::ITE(cond, then_, else_) = lhs.op() {
                if let AstOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
                    Ok(ctx.ite(
                        cond,
                        ctx.ite(
                            rhs_cond,
                            ctx.str_concat(then_, rhs_then)?,
                            ctx.str_concat(then_, rhs_else)?,
                        )?,
                        ctx.ite(
                            rhs_cond,
                            ctx.str_concat(else_, rhs_then)?,
                            ctx.str_concat(else_, rhs_else)?,
                        )?,
                    )?)
                } else {
                    Ok(ctx.ite(
                        cond,
                        ctx.str_concat(then_, &rhs)?,
                        ctx.str_concat(else_, rhs)?,
                    )?)
                }
            } else if let AstOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_concat(&lhs, then_)?,
                    ctx.str_concat(lhs, else_)?,
                )?)
            } else {
                Ok(ctx.str_concat(lhs, rhs)?)
            }
        }
        AstOp::StrSubstr(..) => {
            let base = extract_string_child(children, 0)?;
            let start = extract_bitvec_child(children, 1)?;
            let size = extract_bitvec_child(children, 2)?;

            if let AstOp::ITE(cond, then_, else_) = base.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_substr(then_, &start, &size)?,
                    ctx.str_substr(else_, start, size)?,
                )?)
            } else if let AstOp::ITE(cond, then_, else_) = start.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_substr(&base, then_, &size)?,
                    ctx.str_substr(base, else_, size)?,
                )?)
            } else if let AstOp::ITE(cond, then_, else_) = size.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_substr(&base, &start, then_)?,
                    ctx.str_substr(base, start, else_)?,
                )?)
            } else {
                Ok(ctx.str_substr(base, start, size)?)
            }
        }
        AstOp::StrReplace(..) => {
            let base = extract_string_child(children, 0)?;
            let pattern = extract_string_child(children, 1)?;
            let replacement = extract_string_child(children, 2)?;

            if let AstOp::ITE(cond, then_, else_) = base.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_replace(then_, &pattern, &replacement)?,
                    ctx.str_replace(else_, pattern, replacement)?,
                )?)
            } else if let AstOp::ITE(cond, then_, else_) = pattern.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_replace(&base, then_, &replacement)?,
                    ctx.str_replace(base, else_, replacement)?,
                )?)
            } else if let AstOp::ITE(cond, then_, else_) = replacement.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_replace(&base, &pattern, then_)?,
                    ctx.str_replace(base, pattern, else_)?,
                )?)
            } else {
                Ok(ctx.str_replace(base, pattern, replacement)?)
            }
        }
        AstOp::BVToStr(..) => {
            let inner = extract_bitvec_child(children, 0)?;

            if let AstOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.bv_to_str(then_)?, ctx.bv_to_str(else_)?)?)
            } else {
                Ok(ctx.bv_to_str(inner)?)
            }
        }
        AstOp::ITE(..) => {
            let cond = extract_bool_child(children, 0)?;
            let then_ = extract_string_child(children, 1)?;
            let else_ = extract_string_child(children, 2)?;

            Ok(ctx.ite(cond, then_, else_)?)
        }
        _ => unreachable!("non-string op dispatched to excavate_ite"),
    }
}
