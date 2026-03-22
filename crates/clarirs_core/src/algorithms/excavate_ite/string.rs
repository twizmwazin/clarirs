use super::extract_child;
use crate::prelude::*;

pub(crate) fn excavate_ite<'c>(
    ast: &AstRef<'c>,
    children: &[AstRef<'c>],
) -> Result<AstRef<'c>, ClarirsError> {
    let ctx = ast.context();

    match ast.op() {
        AstOp::StringS(..) | AstOp::StringV(..) => Ok(ast.clone()),
        AstOp::StrConcat(..) => {
            let lhs = extract_child(children, 0)?;
            let rhs = extract_child(children, 1)?;

            if let AstOp::If(cond, then_, else_) = lhs.op() {
                if let AstOp::If(rhs_cond, rhs_then, rhs_else) = rhs.op() {
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
            } else if let AstOp::If(cond, then_, else_) = rhs.op() {
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
            let base = extract_child(children, 0)?;
            let start = extract_child(children, 1)?;
            let size = extract_child(children, 2)?;

            if let AstOp::If(cond, then_, else_) = base.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_substr(then_, &start, &size)?,
                    ctx.str_substr(else_, start, size)?,
                )?)
            } else if let AstOp::If(cond, then_, else_) = start.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_substr(&base, then_, &size)?,
                    ctx.str_substr(base, else_, size)?,
                )?)
            } else if let AstOp::If(cond, then_, else_) = size.op() {
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
            let base = extract_child(children, 0)?;
            let pattern = extract_child(children, 1)?;
            let replacement = extract_child(children, 2)?;

            if let AstOp::If(cond, then_, else_) = base.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_replace(then_, &pattern, &replacement)?,
                    ctx.str_replace(else_, pattern, replacement)?,
                )?)
            } else if let AstOp::If(cond, then_, else_) = pattern.op() {
                Ok(ctx.ite(
                    cond,
                    ctx.str_replace(&base, then_, &replacement)?,
                    ctx.str_replace(base, else_, replacement)?,
                )?)
            } else if let AstOp::If(cond, then_, else_) = replacement.op() {
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
            let inner = extract_child(children, 0)?;

            if let AstOp::If(cond, then_, else_) = inner.op() {
                Ok(ctx.ite(cond, ctx.bv_to_str(then_)?, ctx.bv_to_str(else_)?)?)
            } else {
                Ok(ctx.bv_to_str(inner)?)
            }
        }
        AstOp::If(..) => {
            let cond = extract_child(children, 0)?;
            let then_ = extract_child(children, 1)?;
            let else_ = extract_child(children, 2)?;

            Ok(ctx.ite(cond, then_, else_)?)
        }
        _ => unreachable!(
            "string::excavate_ite called with non-string op: {:?}",
            ast.op()
        ),
    }
}
