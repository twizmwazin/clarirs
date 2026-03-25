//! Shared helper for reconstructing an AST node from its transformed children.

use crate::prelude::*;

fn child<'c>(children: &[AstRef<'c>], index: usize) -> Result<AstRef<'c>, ClarirsError> {
    children
        .get(index)
        .cloned()
        .ok_or(ClarirsError::MissingChild(index))
}

/// Reconstructs an AST node from its operation and transformed children.
///
/// Leaf nodes are returned as-is. Non-leaf nodes are rebuilt using the context
/// factory methods with the provided transformed children.
pub fn reconstruct_node<'c>(
    ctx: &'c Context<'c>,
    ast: &AstRef<'c>,
    children: &[AstRef<'c>],
) -> Result<AstRef<'c>, ClarirsError> {
    match ast.op() {
        // ── Leaves ──────────────────────────────────────────────────
        Op::BoolS(..) | Op::BoolV(..) | Op::BVS(..) | Op::BVV(..) | Op::FPS(..) | Op::FPV(..)
        | Op::StringS(..) | Op::StringV(..) => Ok(ast.clone()),

        // ── Bool logic ──────────────────────────────────────────────
        Op::Not(..) => ctx.not(child(children, 0)?),
        Op::And(args) => {
            let new_args: Vec<_> = (0..args.len())
                .map(|i| child(children, i))
                .collect::<Result<_, _>>()?;
            ctx.and(new_args)
        }
        Op::Or(args) => {
            let new_args: Vec<_> = (0..args.len())
                .map(|i| child(children, i))
                .collect::<Result<_, _>>()?;
            ctx.or(new_args)
        }
        Op::Xor(..) => ctx.xor(child(children, 0)?, child(children, 1)?),
        Op::BoolEq(..) | Op::Eq(..) | Op::FpEq(..) | Op::StrEq(..) => {
            ctx.eq_(child(children, 0)?, child(children, 1)?)
        }
        Op::BoolNeq(..) | Op::Neq(..) | Op::FpNeq(..) | Op::StrNeq(..) => {
            ctx.neq(child(children, 0)?, child(children, 1)?)
        }
        Op::ULT(..) => ctx.ult(child(children, 0)?, child(children, 1)?),
        Op::ULE(..) => ctx.ule(child(children, 0)?, child(children, 1)?),
        Op::UGT(..) => ctx.ugt(child(children, 0)?, child(children, 1)?),
        Op::UGE(..) => ctx.uge(child(children, 0)?, child(children, 1)?),
        Op::SLT(..) => ctx.slt(child(children, 0)?, child(children, 1)?),
        Op::SLE(..) => ctx.sle(child(children, 0)?, child(children, 1)?),
        Op::SGT(..) => ctx.sgt(child(children, 0)?, child(children, 1)?),
        Op::SGE(..) => ctx.sge(child(children, 0)?, child(children, 1)?),
        Op::FpLt(..) => ctx.fp_lt(child(children, 0)?, child(children, 1)?),
        Op::FpLeq(..) => ctx.fp_leq(child(children, 0)?, child(children, 1)?),
        Op::FpGt(..) => ctx.fp_gt(child(children, 0)?, child(children, 1)?),
        Op::FpGeq(..) => ctx.fp_geq(child(children, 0)?, child(children, 1)?),
        Op::FpIsNan(..) => ctx.fp_is_nan(child(children, 0)?),
        Op::FpIsInf(..) => ctx.fp_is_inf(child(children, 0)?),
        Op::StrContains(..) => ctx.str_contains(child(children, 0)?, child(children, 1)?),
        Op::StrPrefixOf(..) => ctx.str_prefix_of(child(children, 0)?, child(children, 1)?),
        Op::StrSuffixOf(..) => ctx.str_suffix_of(child(children, 0)?, child(children, 1)?),
        Op::StrIsDigit(..) => ctx.str_is_digit(child(children, 0)?),
        Op::BoolITE(..) | Op::BVITE(..) | Op::FpITE(..) | Op::StrITE(..) => {
            ctx.ite(child(children, 0)?, child(children, 1)?, child(children, 2)?)
        }

        // ── BitVec ──────────────────────────────────────────────────
        Op::BVNot(..) => ctx.not(child(children, 0)?),
        Op::BVAnd(args) => {
            let new_args: Vec<_> = (0..args.len())
                .map(|i| child(children, i))
                .collect::<Result<_, _>>()?;
            ctx.bv_and_many(new_args)
        }
        Op::BVOr(args) => {
            let new_args: Vec<_> = (0..args.len())
                .map(|i| child(children, i))
                .collect::<Result<_, _>>()?;
            ctx.bv_or_many(new_args)
        }
        Op::BVXor(args) => {
            let new_args: Vec<_> = (0..args.len())
                .map(|i| child(children, i))
                .collect::<Result<_, _>>()?;
            ctx.bv_xor_many(new_args)
        }
        Op::Neg(..) => ctx.neg(child(children, 0)?),
        Op::Add(args) => {
            let new_args: Vec<_> = (0..args.len())
                .map(|i| child(children, i))
                .collect::<Result<_, _>>()?;
            ctx.add_many(new_args)
        }
        Op::Sub(..) => ctx.sub(child(children, 0)?, child(children, 1)?),
        Op::Mul(args) => {
            let new_args: Vec<_> = (0..args.len())
                .map(|i| child(children, i))
                .collect::<Result<_, _>>()?;
            ctx.mul_many(new_args)
        }
        Op::UDiv(..) => ctx.udiv(child(children, 0)?, child(children, 1)?),
        Op::SDiv(..) => ctx.sdiv(child(children, 0)?, child(children, 1)?),
        Op::URem(..) => ctx.urem(child(children, 0)?, child(children, 1)?),
        Op::SRem(..) => ctx.srem(child(children, 0)?, child(children, 1)?),
        Op::ShL(..) => ctx.shl(child(children, 0)?, child(children, 1)?),
        Op::LShR(..) => ctx.lshr(child(children, 0)?, child(children, 1)?),
        Op::AShR(..) => ctx.ashr(child(children, 0)?, child(children, 1)?),
        Op::RotateLeft(..) => ctx.rotate_left(child(children, 0)?, child(children, 1)?),
        Op::RotateRight(..) => ctx.rotate_right(child(children, 0)?, child(children, 1)?),
        Op::ZeroExt(_, size) => ctx.zero_ext(child(children, 0)?, *size),
        Op::SignExt(_, size) => ctx.sign_ext(child(children, 0)?, *size),
        Op::Extract(_, hi, lo) => ctx.extract(child(children, 0)?, *hi, *lo),
        Op::Concat(args) => {
            let new_args: Vec<_> = (0..args.len())
                .map(|i| child(children, i))
                .collect::<Result<_, _>>()?;
            ctx.concat(new_args)
        }
        Op::ByteReverse(..) => ctx.byte_reverse(child(children, 0)?),
        Op::FpToIEEEBV(..) => ctx.fp_to_ieeebv(child(children, 0)?),
        Op::FpToUBV(_, size, fprm) => ctx.fp_to_ubv(child(children, 0)?, *size, *fprm),
        Op::FpToSBV(_, size, fprm) => ctx.fp_to_sbv(child(children, 0)?, *size, *fprm),
        Op::StrLen(..) => ctx.str_len(child(children, 0)?),
        Op::StrIndexOf(..) => {
            ctx.str_index_of(child(children, 0)?, child(children, 1)?, child(children, 2)?)
        }
        Op::StrToBV(..) => ctx.str_to_bv(child(children, 0)?),
        Op::Union(..) => ctx.union(child(children, 0)?, child(children, 1)?),
        Op::Intersection(..) => ctx.intersection(child(children, 0)?, child(children, 1)?),
        Op::Widen(..) => ctx.widen(child(children, 0)?, child(children, 1)?),

        // ── Float ───────────────────────────────────────────────────
        Op::FpNeg(..) => ctx.fp_neg(child(children, 0)?),
        Op::FpAbs(..) => ctx.fp_abs(child(children, 0)?),
        Op::FpAdd(_, _, fprm) => ctx.fp_add(child(children, 0)?, child(children, 1)?, *fprm),
        Op::FpSub(_, _, fprm) => ctx.fp_sub(child(children, 0)?, child(children, 1)?, *fprm),
        Op::FpMul(_, _, fprm) => ctx.fp_mul(child(children, 0)?, child(children, 1)?, *fprm),
        Op::FpDiv(_, _, fprm) => ctx.fp_div(child(children, 0)?, child(children, 1)?, *fprm),
        Op::FpSqrt(_, fprm) => ctx.fp_sqrt(child(children, 0)?, *fprm),
        Op::FpToFp(_, fsort, fprm) => ctx.fp_to_fp(child(children, 0)?, *fsort, *fprm),
        Op::FpFP(..) => ctx.fp_fp(child(children, 0)?, child(children, 1)?, child(children, 2)?),
        Op::BvToFp(_, fsort) => ctx.bv_to_fp(child(children, 0)?, *fsort),
        Op::BvToFpSigned(_, fsort, fprm) => {
            ctx.bv_to_fp_signed(child(children, 0)?, *fsort, *fprm)
        }
        Op::BvToFpUnsigned(_, fsort, fprm) => {
            ctx.bv_to_fp_unsigned(child(children, 0)?, *fsort, *fprm)
        }

        // ── String ──────────────────────────────────────────────────
        Op::StrConcat(..) => ctx.str_concat(child(children, 0)?, child(children, 1)?),
        Op::StrSubstr(..) => {
            ctx.str_substr(child(children, 0)?, child(children, 1)?, child(children, 2)?)
        }
        Op::StrReplace(..) => {
            ctx.str_replace(child(children, 0)?, child(children, 1)?, child(children, 2)?)
        }
        Op::BVToStr(..) => ctx.bv_to_str(child(children, 0)?),
    }
}
