//! Shared helper for reconstructing an AstRef node from its transformed children.
//! Used by the `replace` algorithm.

use crate::prelude::*;

/// Reconstructs an `AstRef` node from its operation and transformed children.
///
/// Leaf nodes are returned as-is. Non-leaf nodes are rebuilt using the context
/// factory methods with the provided transformed children.
pub fn reconstruct_node<'c>(
    ctx: &'c Context<'c>,
    ast: &AstRef<'c>,
    children: &[AstRef<'c>],
) -> Result<AstRef<'c>, ClarirsError> {
    match ast.op() {
        // === Leaf nodes ===
        AstOp::BoolS(..)
        | AstOp::BoolV(..)
        | AstOp::BVS(..)
        | AstOp::BVV(..)
        | AstOp::FPS(..)
        | AstOp::FPV(..)
        | AstOp::StringS(..)
        | AstOp::StringV(..) => Ok(ast.clone()),

        // === Cross-sort operations ===
        AstOp::Not(..) => ctx.not(children[0].clone()),
        AstOp::And(..) => ctx.and(children.to_vec()),
        AstOp::Or(..) => ctx.or(children.to_vec()),
        AstOp::Xor(..) => ctx.bv_xor_many(children.to_vec()),
        AstOp::Eq(..) => ctx.eq_(children[0].clone(), children[1].clone()),
        AstOp::Neq(..) => ctx.neq(children[0].clone(), children[1].clone()),
        AstOp::If(..) => ctx.ite(
            children[0].clone(),
            children[1].clone(),
            children[2].clone(),
        ),

        // === BV arithmetic ===
        AstOp::Neg(..) => ctx.neg(children[0].clone()),
        AstOp::Add(..) => ctx.add_many(children.to_vec()),
        AstOp::Sub(..) => ctx.sub(children[0].clone(), children[1].clone()),
        AstOp::Mul(..) => ctx.mul_many(children.to_vec()),
        AstOp::UDiv(..) => ctx.udiv(children[0].clone(), children[1].clone()),
        AstOp::SDiv(..) => ctx.sdiv(children[0].clone(), children[1].clone()),
        AstOp::URem(..) => ctx.urem(children[0].clone(), children[1].clone()),
        AstOp::SRem(..) => ctx.srem(children[0].clone(), children[1].clone()),

        // === BV shifts/rotates ===
        AstOp::ShL(..) => ctx.shl(children[0].clone(), children[1].clone()),
        AstOp::LShR(..) => ctx.lshr(children[0].clone(), children[1].clone()),
        AstOp::AShR(..) => ctx.ashr(children[0].clone(), children[1].clone()),
        AstOp::RotateLeft(..) => ctx.rotate_left(children[0].clone(), children[1].clone()),
        AstOp::RotateRight(..) => ctx.rotate_right(children[0].clone(), children[1].clone()),

        // === BV extraction/extension ===
        AstOp::ZeroExt(_, size) => ctx.zero_ext(children[0].clone(), *size),
        AstOp::SignExt(_, size) => ctx.sign_ext(children[0].clone(), *size),
        AstOp::Extract(_, hi, lo) => ctx.extract(children[0].clone(), *hi, *lo),
        AstOp::Concat(..) => ctx.concat(children.to_vec()),
        AstOp::ByteReverse(..) => ctx.byte_reverse(children[0].clone()),

        // === BV comparisons ===
        AstOp::ULT(..) => ctx.ult(children[0].clone(), children[1].clone()),
        AstOp::ULE(..) => ctx.ule(children[0].clone(), children[1].clone()),
        AstOp::UGT(..) => ctx.ugt(children[0].clone(), children[1].clone()),
        AstOp::UGE(..) => ctx.uge(children[0].clone(), children[1].clone()),
        AstOp::SLT(..) => ctx.slt(children[0].clone(), children[1].clone()),
        AstOp::SLE(..) => ctx.sle(children[0].clone(), children[1].clone()),
        AstOp::SGT(..) => ctx.sgt(children[0].clone(), children[1].clone()),
        AstOp::SGE(..) => ctx.sge(children[0].clone(), children[1].clone()),

        // === Float operations ===
        AstOp::FpNeg(..) => ctx.fp_neg(children[0].clone()),
        AstOp::FpAbs(..) => ctx.fp_abs(children[0].clone()),
        AstOp::FpAdd(_, _, fprm) => ctx.fp_add(children[0].clone(), children[1].clone(), *fprm),
        AstOp::FpSub(_, _, fprm) => ctx.fp_sub(children[0].clone(), children[1].clone(), *fprm),
        AstOp::FpMul(_, _, fprm) => ctx.fp_mul(children[0].clone(), children[1].clone(), *fprm),
        AstOp::FpDiv(_, _, fprm) => ctx.fp_div(children[0].clone(), children[1].clone(), *fprm),
        AstOp::FpSqrt(_, fprm) => ctx.fp_sqrt(children[0].clone(), *fprm),
        AstOp::FpToFp(_, fsort, fprm) => ctx.fp_to_fp(children[0].clone(), *fsort, *fprm),
        AstOp::FpFP(..) => ctx.fp_fp(
            children[0].clone(),
            children[1].clone(),
            children[2].clone(),
        ),
        AstOp::BvToFp(_, fsort) => ctx.bv_to_fp(children[0].clone(), *fsort),
        AstOp::BvToFpSigned(_, fsort, fprm) => {
            ctx.bv_to_fp_signed(children[0].clone(), *fsort, *fprm)
        }
        AstOp::BvToFpUnsigned(_, fsort, fprm) => {
            ctx.bv_to_fp_unsigned(children[0].clone(), *fsort, *fprm)
        }

        // === Float comparisons ===
        AstOp::FpLt(..) => ctx.fp_lt(children[0].clone(), children[1].clone()),
        AstOp::FpLeq(..) => ctx.fp_leq(children[0].clone(), children[1].clone()),
        AstOp::FpGt(..) => ctx.fp_gt(children[0].clone(), children[1].clone()),
        AstOp::FpGeq(..) => ctx.fp_geq(children[0].clone(), children[1].clone()),
        AstOp::FpIsNan(..) => ctx.fp_is_nan(children[0].clone()),
        AstOp::FpIsInf(..) => ctx.fp_is_inf(children[0].clone()),

        // === Float-BV conversions ===
        AstOp::FpToIEEEBV(..) => ctx.fp_to_ieeebv(children[0].clone()),
        AstOp::FpToUBV(_, size, fprm) => ctx.fp_to_ubv(children[0].clone(), *size, *fprm),
        AstOp::FpToSBV(_, size, fprm) => ctx.fp_to_sbv(children[0].clone(), *size, *fprm),

        // === String operations ===
        AstOp::StrConcat(..) => ctx.str_concat(children[0].clone(), children[1].clone()),
        AstOp::StrSubstr(..) => ctx.str_substr(
            children[0].clone(),
            children[1].clone(),
            children[2].clone(),
        ),
        AstOp::StrReplace(..) => ctx.str_replace(
            children[0].clone(),
            children[1].clone(),
            children[2].clone(),
        ),
        AstOp::BVToStr(..) => ctx.bv_to_str(children[0].clone()),
        AstOp::StrLen(..) => ctx.str_len(children[0].clone()),
        AstOp::StrIndexOf(..) => ctx.str_index_of(
            children[0].clone(),
            children[1].clone(),
            children[2].clone(),
        ),
        AstOp::StrToBV(..) => ctx.str_to_bv(children[0].clone()),

        // === String comparisons ===
        AstOp::StrContains(..) => ctx.str_contains(children[0].clone(), children[1].clone()),
        AstOp::StrPrefixOf(..) => ctx.str_prefix_of(children[0].clone(), children[1].clone()),
        AstOp::StrSuffixOf(..) => ctx.str_suffix_of(children[0].clone(), children[1].clone()),
        AstOp::StrIsDigit(..) => ctx.str_is_digit(children[0].clone()),

        // === VSA operations ===
        AstOp::Union(..) => ctx.union(children[0].clone(), children[1].clone()),
        AstOp::Intersection(..) => ctx.intersection(children[0].clone(), children[1].clone()),
        AstOp::Widen(..) => ctx.widen(children[0].clone(), children[1].clone()),
    }
}
