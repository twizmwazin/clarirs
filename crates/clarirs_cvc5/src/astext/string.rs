use clarirs_core::prelude::*;
use cvc5_rs::{Kind, Term, TermManager};

use super::AstExtCvc5;

pub(crate) fn to_cvc5(
    tm: &TermManager,
    ast: &StringAst,
    children: &[Term],
) -> Result<Term, ClarirsError> {
    Ok(match ast.op() {
        StringOp::StringS(s) => {
            let sort = tm.string_sort();
            tm.mk_const(sort, s.as_str())
        }
        StringOp::StringV(s) => tm.mk_string(s, false),
        StringOp::StrConcat(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_STRING_CONCAT, &[a, b])
        }
        StringOp::StrSubstr(..) => {
            let a = children[0].clone();
            let offset_bv = children[1].clone();
            let len_bv = children[2].clone();
            // Convert BV to int
            let offset_int = tm.mk_term(Kind::CVC5_KIND_BITVECTOR_TO_NAT, &[offset_bv]);
            let len_int = tm.mk_term(Kind::CVC5_KIND_BITVECTOR_TO_NAT, &[len_bv]);
            tm.mk_term(Kind::CVC5_KIND_STRING_SUBSTR, &[a, offset_int, len_int])
        }
        StringOp::StrReplace(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            let c = children[2].clone();
            tm.mk_term(Kind::CVC5_KIND_STRING_REPLACE, &[a, b, c])
        }
        StringOp::BVToStr(_) => {
            let a = children[0].clone();
            let int_val = tm.mk_term(Kind::CVC5_KIND_BITVECTOR_TO_NAT, &[a]);
            tm.mk_term(Kind::CVC5_KIND_STRING_FROM_INT, &[int_val])
        }
        StringOp::ITE(cond, then, else_) => {
            let cond = cond.to_cvc5(tm)?;
            let then = then.to_cvc5(tm)?;
            let else_ = else_.to_cvc5(tm)?;
            tm.mk_term(Kind::CVC5_KIND_ITE, &[cond, then, else_])
        }
    })
}

pub(crate) fn from_cvc5<'c>(
    ctx: &'c Context<'c>,
    tm: &TermManager,
    term: &Term,
) -> Result<StringAst<'c>, ClarirsError> {
    let sort = term.sort();
    if !sort.is_string() {
        return Err(ClarirsError::ConversionError(
            "expected a string term".to_string(),
        ));
    }

    let kind = term.kind();
    match kind {
        Kind::CVC5_KIND_CONST_STRING => {
            // string_value returns Vec<u32> (wchar_t code points)
            let code_points = term.string_value();
            let s: String = code_points
                .iter()
                .filter_map(|&cp| char::from_u32(cp as u32))
                .collect();
            ctx.stringv(s)
        }
        Kind::CVC5_KIND_CONSTANT => {
            let name = term.symbol();
            ctx.strings(name)
        }
        Kind::CVC5_KIND_STRING_CONCAT => {
            let a = StringAst::from_cvc5(ctx, tm, &term.child(0))?;
            let b = StringAst::from_cvc5(ctx, tm, &term.child(1))?;
            ctx.str_concat(a, b)
        }
        Kind::CVC5_KIND_STRING_SUBSTR => {
            let a = StringAst::from_cvc5(ctx, tm, &term.child(0))?;
            // Offset and length are ints, convert to BV
            let offset_int = term.child(1);
            let len_int = term.child(2);
            // Convert int to bv64
            let op = tm.mk_op(Kind::CVC5_KIND_INT_TO_BITVECTOR, &[64]);
            let offset_bv = tm.mk_term_from_op(op.clone(), &[offset_int]);
            let len_bv = tm.mk_term_from_op(op, &[len_int]);
            let offset = BitVecAst::from_cvc5(ctx, tm, &offset_bv)?;
            let len = BitVecAst::from_cvc5(ctx, tm, &len_bv)?;
            ctx.str_substr(a, offset, len)
        }
        Kind::CVC5_KIND_STRING_REPLACE => {
            let a = StringAst::from_cvc5(ctx, tm, &term.child(0))?;
            let b = StringAst::from_cvc5(ctx, tm, &term.child(1))?;
            let c = StringAst::from_cvc5(ctx, tm, &term.child(2))?;
            ctx.str_replace(a, b, c)
        }
        Kind::CVC5_KIND_STRING_FROM_INT => {
            // str.from_int(bv2nat(bv)) -> BVToStr(bv)
            let inner = term.child(0);
            let inner_kind = inner.kind();
            if inner_kind == Kind::CVC5_KIND_BITVECTOR_TO_NAT {
                let bv = BitVecAst::from_cvc5(ctx, tm, &inner.child(0))?;
                ctx.bv_to_str(bv)
            } else {
                Err(ClarirsError::ConversionError(
                    "expected bv2nat inside str.from_int".to_string(),
                ))
            }
        }
        Kind::CVC5_KIND_ITE => {
            let cond = super::bool::from_cvc5(ctx, tm, &term.child(0))?;
            let then = StringAst::from_cvc5(ctx, tm, &term.child(1))?;
            let else_ = StringAst::from_cvc5(ctx, tm, &term.child(2))?;
            ctx.ite(cond, then, else_)
        }
        _ => Err(ClarirsError::ConversionError(format!(
            "Failed converting from cvc5: unknown kind for string: {:?}",
            kind
        ))),
    }
}
