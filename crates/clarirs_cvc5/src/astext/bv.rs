use clarirs_core::{ast::bitvec::BitVecOpExt, prelude::*};
use cvc5_rs::{Kind, Term, TermManager};

use super::AstExtCvc5;

pub(crate) fn to_cvc5(
    tm: &TermManager,
    ast: &BitVecAst,
    children: &[Term],
) -> Result<Term, ClarirsError> {
    Ok(match ast.op() {
        BitVecOp::BVS(s, w) => {
            let sort = tm.mk_bv_sort(*w);
            tm.mk_const(sort, s.as_str())
        }
        BitVecOp::BVV(v) => {
            let width = v.len();
            let numeral = v.to_biguint().to_string();
            tm.mk_bv_from_str(width, &numeral, 10)
        }
        BitVecOp::Not(..) => {
            let a = children[0].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_NOT, &[a])
        }
        BitVecOp::Neg(..) => {
            let a = children[0].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_NEG, &[a])
        }
        BitVecOp::And(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_AND, &[a, b])
        }
        BitVecOp::Or(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_OR, &[a, b])
        }
        BitVecOp::Xor(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_XOR, &[a, b])
        }
        BitVecOp::Add(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_ADD, &[a, b])
        }
        BitVecOp::Sub(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_SUB, &[a, b])
        }
        BitVecOp::Mul(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_MULT, &[a, b])
        }
        BitVecOp::UDiv(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_UDIV, &[a, b])
        }
        BitVecOp::SDiv(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_SDIV, &[a, b])
        }
        BitVecOp::URem(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_UREM, &[a, b])
        }
        BitVecOp::SRem(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_SREM, &[a, b])
        }
        BitVecOp::ShL(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_SHL, &[a, b])
        }
        BitVecOp::LShR(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_LSHR, &[a, b])
        }
        BitVecOp::AShR(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_ASHR, &[a, b])
        }
        BitVecOp::RotateLeft(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_ROTATE_LEFT, &[a, b])
        }
        BitVecOp::RotateRight(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_ROTATE_RIGHT, &[a, b])
        }
        BitVecOp::ZeroExt(_, i) => {
            let a = children[0].clone();
            let op = tm.mk_op(Kind::CVC5_KIND_BITVECTOR_ZERO_EXTEND, &[*i]);
            tm.mk_term_from_op(op, &[a])
        }
        BitVecOp::SignExt(_, i) => {
            let a = children[0].clone();
            let op = tm.mk_op(Kind::CVC5_KIND_BITVECTOR_SIGN_EXTEND, &[*i]);
            tm.mk_term_from_op(op, &[a])
        }
        BitVecOp::Extract(a_ast, high, low) => {
            if high >= &a_ast.size() {
                return Err(ClarirsError::ConversionError(
                    "high index is greater than bitvector size".to_string(),
                ));
            }
            if low >= &a_ast.size() {
                return Err(ClarirsError::ConversionError(
                    "low index is greater than bitvector size".to_string(),
                ));
            }
            if low > high {
                return Err(ClarirsError::ConversionError(
                    "low index is greater than high index".to_string(),
                ));
            }
            let a = children[0].clone();
            let op = tm.mk_op(Kind::CVC5_KIND_BITVECTOR_EXTRACT, &[*high, *low]);
            tm.mk_term_from_op(op, &[a])
        }
        BitVecOp::Concat(args) => {
            if args.is_empty() {
                return Err(ClarirsError::InvalidArgumentsWithMessage(
                    "Concat requires at least one argument".to_string(),
                ));
            }
            // cvc5's concat is n-ary
            if children.len() == 1 {
                children[0].clone()
            } else {
                tm.mk_term(Kind::CVC5_KIND_BITVECTOR_CONCAT, children)
            }
        }
        BitVecOp::ByteReverse(a_ast) => {
            let size = a_ast.size();
            if size == 0 || size % 8 != 0 {
                return Err(ClarirsError::ConversionError(
                    "reverse only supports bitvectors with size multiple of 8".to_string(),
                ));
            }

            let child_term = children[0].clone();
            let num_bytes = size / 8;

            // Extract the last byte (lowest bits) as the initial accumulator
            let extract_op = tm.mk_op(Kind::CVC5_KIND_BITVECTOR_EXTRACT, &[7, 0]);
            let mut result = tm.mk_term_from_op(extract_op, &[child_term.clone()]);

            // Extract remaining bytes in reverse order and concat
            for i in 1..num_bytes {
                let high = (i + 1) * 8 - 1;
                let low = i * 8;
                let byte_op = tm.mk_op(Kind::CVC5_KIND_BITVECTOR_EXTRACT, &[high, low]);
                let byte = tm.mk_term_from_op(byte_op, &[child_term.clone()]);
                result = tm.mk_term(Kind::CVC5_KIND_BITVECTOR_CONCAT, &[result, byte]);
            }

            result
        }
        BitVecOp::ITE(..) => {
            let cond = children[0].clone();
            let then = children[1].clone();
            let else_ = children[2].clone();
            tm.mk_term(Kind::CVC5_KIND_ITE, &[cond, then, else_])
        }
        BitVecOp::FpToIEEEBV(..) => {
            // cvc5 doesn't have a direct fpToIEEEBV kind.
            return Err(ClarirsError::UnsupportedOperation(
                "fpToIEEEBV is not directly supported in cvc5 backend".to_string(),
            ));
        }
        BitVecOp::FpToUBV(_, size, rm) => {
            let rm_term = super::float::fprm_to_cvc5(tm, *rm);
            let a = children[0].clone();
            let op = tm.mk_op(Kind::CVC5_KIND_FLOATINGPOINT_TO_UBV, &[*size]);
            tm.mk_term_from_op(op, &[rm_term, a])
        }
        BitVecOp::FpToSBV(_, size, rm) => {
            let rm_term = super::float::fprm_to_cvc5(tm, *rm);
            let a = children[0].clone();
            let op = tm.mk_op(Kind::CVC5_KIND_FLOATINGPOINT_TO_SBV, &[*size]);
            tm.mk_term_from_op(op, &[rm_term, a])
        }
        BitVecOp::StrLen(..) => {
            let a = children[0].clone();
            let str_len = tm.mk_term(Kind::CVC5_KIND_STRING_LENGTH, &[a]);
            // Convert int to bitvector of width 64
            let op = tm.mk_op(Kind::CVC5_KIND_INT_TO_BITVECTOR, &[64]);
            tm.mk_term_from_op(op, &[str_len])
        }
        BitVecOp::StrIndexOf(..) => {
            let haystack = children[0].clone();
            let needle = children[1].clone();
            let offset_bv = children[2].clone();
            // Convert bv offset to int
            let offset_int = tm.mk_term(Kind::CVC5_KIND_BITVECTOR_TO_NAT, &[offset_bv]);
            let index_int = tm.mk_term(Kind::CVC5_KIND_STRING_INDEXOF, &[haystack, needle, offset_int]);
            let op = tm.mk_op(Kind::CVC5_KIND_INT_TO_BITVECTOR, &[64]);
            tm.mk_term_from_op(op, &[index_int])
        }
        BitVecOp::StrToBV(..) => {
            let a = children[0].clone();
            let int_val = tm.mk_term(Kind::CVC5_KIND_STRING_TO_INT, &[a]);
            let op = tm.mk_op(Kind::CVC5_KIND_INT_TO_BITVECTOR, &[64]);
            tm.mk_term_from_op(op, &[int_val])
        }
        BitVecOp::Union(..) | BitVecOp::Intersection(..) | BitVecOp::Widen(..) => {
            return Err(ClarirsError::ConversionError(
                "vsa types are not currently supported in the cvc5 backend".to_string(),
            ));
        }
    })
}

pub(crate) fn from_cvc5<'c>(
    ctx: &'c Context<'c>,
    tm: &TermManager,
    term: &Term,
) -> Result<BitVecAst<'c>, ClarirsError> {
    let sort = term.sort();
    if !sort.is_bv() {
        return Err(ClarirsError::ConversionError(
            "expected a bitvector term".to_string(),
        ));
    }

    let width = sort.bv_size();
    let kind = term.kind();

    match kind {
        Kind::CVC5_KIND_CONST_BITVECTOR => {
            let val_str = term.bv_value(10);
            let bv = BitVec::from_str(&val_str, width).map_err(|_| {
                ClarirsError::ConversionError("Failed to parse bitvector value".to_string())
            })?;
            ctx.bvv(bv)
        }
        Kind::CVC5_KIND_CONSTANT => {
            let name = term.symbol();
            ctx.bvs(name, width)
        }
        Kind::CVC5_KIND_BITVECTOR_NOT => {
            let inner = BitVecAst::from_cvc5(ctx, tm, &term.child(0))?;
            ctx.not(inner)
        }
        Kind::CVC5_KIND_BITVECTOR_NEG => {
            let inner = BitVecAst::from_cvc5(ctx, tm, &term.child(0))?;
            ctx.neg(inner)
        }
        Kind::CVC5_KIND_BITVECTOR_AND
        | Kind::CVC5_KIND_BITVECTOR_OR
        | Kind::CVC5_KIND_BITVECTOR_XOR
        | Kind::CVC5_KIND_BITVECTOR_ADD
        | Kind::CVC5_KIND_BITVECTOR_SUB
        | Kind::CVC5_KIND_BITVECTOR_MULT
        | Kind::CVC5_KIND_BITVECTOR_UDIV
        | Kind::CVC5_KIND_BITVECTOR_SDIV
        | Kind::CVC5_KIND_BITVECTOR_UREM
        | Kind::CVC5_KIND_BITVECTOR_SREM
        | Kind::CVC5_KIND_BITVECTOR_SHL
        | Kind::CVC5_KIND_BITVECTOR_LSHR
        | Kind::CVC5_KIND_BITVECTOR_ASHR => {
            let num_children = term.num_children();
            if num_children < 2 {
                return Err(ClarirsError::ConversionError(format!(
                    "Expected binary operation to have at least 2 arguments, got {}",
                    num_children
                )));
            }

            let apply_op =
                |ctx: &'c Context<'c>,
                 a: BitVecAst<'c>,
                 b: BitVecAst<'c>|
                 -> Result<BitVecAst<'c>, ClarirsError> {
                    match kind {
                        Kind::CVC5_KIND_BITVECTOR_AND => ctx.bv_and(a, b),
                        Kind::CVC5_KIND_BITVECTOR_OR => ctx.bv_or(a, b),
                        Kind::CVC5_KIND_BITVECTOR_XOR => ctx.xor(a, b),
                        Kind::CVC5_KIND_BITVECTOR_ADD => ctx.add(a, b),
                        Kind::CVC5_KIND_BITVECTOR_SUB => ctx.sub(a, b),
                        Kind::CVC5_KIND_BITVECTOR_MULT => ctx.mul(a, b),
                        Kind::CVC5_KIND_BITVECTOR_UDIV => ctx.udiv(a, b),
                        Kind::CVC5_KIND_BITVECTOR_SDIV => ctx.sdiv(a, b),
                        Kind::CVC5_KIND_BITVECTOR_UREM => ctx.urem(a, b),
                        Kind::CVC5_KIND_BITVECTOR_SREM => ctx.srem(a, b),
                        Kind::CVC5_KIND_BITVECTOR_SHL => ctx.shl(a, b),
                        Kind::CVC5_KIND_BITVECTOR_LSHR => ctx.lshr(a, b),
                        Kind::CVC5_KIND_BITVECTOR_ASHR => ctx.ashr(a, b),
                        _ => unreachable!(),
                    }
                };

            let mut result = BitVecAst::from_cvc5(ctx, tm, &term.child(0))?;
            for i in 1..num_children {
                let b = BitVecAst::from_cvc5(ctx, tm, &term.child(i))?;
                result = apply_op(ctx, result, b)?;
            }
            Ok(result)
        }
        Kind::CVC5_KIND_BITVECTOR_ROTATE_LEFT => {
            let a = BitVecAst::from_cvc5(ctx, tm, &term.child(0))?;
            let b = BitVecAst::from_cvc5(ctx, tm, &term.child(1))?;
            ctx.rotate_left(a, b)
        }
        Kind::CVC5_KIND_BITVECTOR_ROTATE_RIGHT => {
            let a = BitVecAst::from_cvc5(ctx, tm, &term.child(0))?;
            let b = BitVecAst::from_cvc5(ctx, tm, &term.child(1))?;
            ctx.rotate_right(a, b)
        }
        Kind::CVC5_KIND_BITVECTOR_ZERO_EXTEND => {
            let inner = BitVecAst::from_cvc5(ctx, tm, &term.child(0))?;
            let extend_amount = width - inner.size();
            ctx.zero_ext(&inner, extend_amount)
        }
        Kind::CVC5_KIND_BITVECTOR_SIGN_EXTEND => {
            let inner = BitVecAst::from_cvc5(ctx, tm, &term.child(0))?;
            let extend_amount = width - inner.size();
            ctx.sign_ext(inner, extend_amount)
        }
        Kind::CVC5_KIND_BITVECTOR_EXTRACT => {
            let inner = BitVecAst::from_cvc5(ctx, tm, &term.child(0))?;
            // Get extract indices from the operator
            let op = term.op();
            let high_term = op.index(0);
            let low_term = op.index(1);
            let high = high_term.uint32_value();
            let low = low_term.uint32_value();
            ctx.extract(inner, high, low)
        }
        Kind::CVC5_KIND_BITVECTOR_CONCAT => {
            let num = term.num_children();
            let mut args = Vec::with_capacity(num);
            for i in 0..num {
                let val = BitVecAst::from_cvc5(ctx, tm, &term.child(i))?;
                args.push(val);
            }
            ctx.concat(args)
        }
        Kind::CVC5_KIND_ITE => {
            let cond = super::bool::from_cvc5(ctx, tm, &term.child(0))?;
            let then = BitVecAst::from_cvc5(ctx, tm, &term.child(1))?;
            let else_ = BitVecAst::from_cvc5(ctx, tm, &term.child(2))?;
            ctx.ite(cond, then, else_)
        }
        _ => Err(ClarirsError::ConversionError(format!(
            "Failed converting from cvc5: unknown kind for bitvec: {:?}",
            kind
        ))),
    }
}
