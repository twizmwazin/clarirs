use super::{extract_bitvec_child, extract_bool_child, extract_string_child};
use crate::prelude::*;

pub(crate) fn excavate_ite<'c>(
    ast: &StringAst<'c>,
    children: &[DynAst<'c>],
) -> Result<StringAst<'c>, ClarirsError> {
    let ctx = ast.context();

    match ast.op() {
        StringOp::StringS(..) | StringOp::StringV(..) => Ok(ast.clone()),
        StringOp::StrConcat(..) => {
            let lhs = extract_string_child(children, 0)?;
            let rhs = extract_string_child(children, 1)?;

            if let StringOp::ITE(cond, then_, else_) = lhs.op() {
                if let StringOp::ITE(rhs_cond, rhs_then, rhs_else) = rhs.op() {
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
            } else if let StringOp::ITE(cond, then_, else_) = rhs.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_concat(&lhs, then_)?,
                    ctx.str_concat(lhs, else_)?,
                )?)
            } else {
                Ok(ctx.str_concat(lhs, rhs)?)
            }
        }
        StringOp::StrSubstr(..) => {
            let base = extract_string_child(children, 0)?;
            let start = extract_bitvec_child(children, 1)?;
            let size = extract_bitvec_child(children, 2)?;

            if let StringOp::ITE(cond, then_, else_) = base.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_substr(then_, &start, &size)?,
                    ctx.str_substr(else_, start, size)?,
                )?)
            } else if let BitVecOp::ITE(cond, then_, else_) = start.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_substr(&base, then_, &size)?,
                    ctx.str_substr(base, else_, size)?,
                )?)
            } else if let BitVecOp::ITE(cond, then_, else_) = size.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_substr(&base, &start, then_)?,
                    ctx.str_substr(base, start, else_)?,
                )?)
            } else {
                Ok(ctx.str_substr(base, start, size)?)
            }
        }
        StringOp::StrReplace(..) => {
            let base = extract_string_child(children, 0)?;
            let pattern = extract_string_child(children, 1)?;
            let replacement = extract_string_child(children, 2)?;

            if let StringOp::ITE(cond, then_, else_) = base.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_replace(then_, &pattern, &replacement)?,
                    ctx.str_replace(else_, pattern, replacement)?,
                )?)
            } else if let StringOp::ITE(cond, then_, else_) = pattern.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_replace(&base, then_, &replacement)?,
                    ctx.str_replace(base, else_, replacement)?,
                )?)
            } else if let StringOp::ITE(cond, then_, else_) = replacement.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_replace(&base, &pattern, then_)?,
                    ctx.str_replace(base, pattern, else_)?,
                )?)
            } else {
                Ok(ctx.str_replace(base, pattern, replacement)?)
            }
        }
        StringOp::BVToStr(..) => {
            let inner = extract_bitvec_child(children, 0)?;

            if let BitVecOp::ITE(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.bv_to_str(then_)?,
                    ctx.bv_to_str(else_)?,
                )?)
            } else {
                Ok(ctx.bv_to_str(inner)?)
            }
        }
        StringOp::ITE(..) => {
            let cond = extract_bool_child(children, 0)?;
            let then_ = extract_string_child(children, 1)?;
            let else_ = extract_string_child(children, 2)?;

            Ok(ctx.ite(cond, then_, else_)?)
        }
    }
}
