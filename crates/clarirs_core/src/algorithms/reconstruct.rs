//! Shared helper for reconstructing a DynAst node from its transformed children.
//! Used by the `replace` algorithm.

use crate::{
    algorithms::post_order::{bitvec_child, bool_child, float_child, string_child},
    prelude::*,
};

/// Reconstructs a `DynAst` node from its operation and transformed children.
///
/// Leaf nodes are returned as-is. Non-leaf nodes are rebuilt using the context
/// factory methods with the provided transformed children.
pub fn reconstruct_node<'c>(
    ctx: &'c Context<'c>,
    ast: &DynAst<'c>,
    children: &[DynAst<'c>],
) -> Result<DynAst<'c>, ClarirsError> {
    match ast {
        DynAst::Boolean(bool_ast) => match bool_ast.op() {
            BooleanOp::BoolS(..) | BooleanOp::BoolV(..) => Ok(bool_ast.clone()),
            BooleanOp::Not(..) => ctx.not(bool_child(children, 0)?),
            BooleanOp::And(..) => {
                let args: Vec<_> = children
                    .iter()
                    .map(|c| bool_child(std::slice::from_ref(c), 0))
                    .collect::<Result<_, _>>()?;
                ctx.and(args)
            }
            BooleanOp::Or(..) => {
                let args: Vec<_> = children
                    .iter()
                    .map(|c| bool_child(std::slice::from_ref(c), 0))
                    .collect::<Result<_, _>>()?;
                ctx.or(args)
            }
            BooleanOp::Xor(..) => ctx.xor(bool_child(children, 0)?, bool_child(children, 1)?),
            BooleanOp::BoolEq(..) => ctx.eq_(bool_child(children, 0)?, bool_child(children, 1)?),
            BooleanOp::BoolNeq(..) => {
                let args: Vec<_> = children
                    .iter()
                    .map(|c| bool_child(std::slice::from_ref(c), 0))
                    .collect::<Result<_, _>>()?;
                ctx.distinct(args)
            }
            BooleanOp::Eq(..) => ctx.eq_(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BooleanOp::Neq(..) => {
                let args: Vec<_> = children
                    .iter()
                    .map(|c| bitvec_child(std::slice::from_ref(c), 0))
                    .collect::<Result<_, _>>()?;
                ctx.distinct(args)
            }
            BooleanOp::ULT(..) => ctx.ult(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BooleanOp::ULE(..) => ctx.ule(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BooleanOp::UGT(..) => ctx.ugt(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BooleanOp::UGE(..) => ctx.uge(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BooleanOp::SLT(..) => ctx.slt(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BooleanOp::SLE(..) => ctx.sle(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BooleanOp::SGT(..) => ctx.sgt(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BooleanOp::SGE(..) => ctx.sge(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BooleanOp::FpEq(..) => ctx.fp_eq(float_child(children, 0)?, float_child(children, 1)?),
            BooleanOp::FpNeq(..) => {
                let args: Vec<_> = children
                    .iter()
                    .map(|c| float_child(std::slice::from_ref(c), 0))
                    .collect::<Result<_, _>>()?;
                ctx.distinct(args)
            }
            BooleanOp::FpLt(..) => ctx.fp_lt(float_child(children, 0)?, float_child(children, 1)?),
            BooleanOp::FpLeq(..) => {
                ctx.fp_leq(float_child(children, 0)?, float_child(children, 1)?)
            }
            BooleanOp::FpGt(..) => ctx.fp_gt(float_child(children, 0)?, float_child(children, 1)?),
            BooleanOp::FpGeq(..) => {
                ctx.fp_geq(float_child(children, 0)?, float_child(children, 1)?)
            }
            BooleanOp::FpIsNan(..) => ctx.fp_is_nan(float_child(children, 0)?),
            BooleanOp::FpIsInf(..) => ctx.fp_is_inf(float_child(children, 0)?),
            BooleanOp::StrContains(..) => {
                ctx.str_contains(string_child(children, 0)?, string_child(children, 1)?)
            }
            BooleanOp::StrPrefixOf(..) => {
                ctx.str_prefix_of(string_child(children, 0)?, string_child(children, 1)?)
            }
            BooleanOp::StrSuffixOf(..) => {
                ctx.str_suffix_of(string_child(children, 0)?, string_child(children, 1)?)
            }
            BooleanOp::StrIsDigit(..) => ctx.str_is_digit(string_child(children, 0)?),
            BooleanOp::StrEq(..) => {
                ctx.str_eq(string_child(children, 0)?, string_child(children, 1)?)
            }
            BooleanOp::StrNeq(..) => {
                let args: Vec<_> = children
                    .iter()
                    .map(|c| string_child(std::slice::from_ref(c), 0))
                    .collect::<Result<_, _>>()?;
                ctx.distinct(args)
            }
            BooleanOp::ITE(..) => ctx.ite(
                bool_child(children, 0)?,
                bool_child(children, 1)?,
                bool_child(children, 2)?,
            ),
        }
        .map(DynAst::Boolean),
        DynAst::BitVec(bv_ast) => match bv_ast.op() {
            BitVecOp::BVS(..) | BitVecOp::BVV(..) => Ok(bv_ast.clone()),
            BitVecOp::Not(..) => ctx.not(bitvec_child(children, 0)?),
            BitVecOp::And(args) => {
                let new_args: Vec<_> = (0..args.len())
                    .map(|i| bitvec_child(children, i))
                    .collect::<Result<_, _>>()?;
                ctx.bv_and_many(new_args)
            }
            BitVecOp::Or(args) => {
                let new_args: Vec<_> = (0..args.len())
                    .map(|i| bitvec_child(children, i))
                    .collect::<Result<_, _>>()?;
                ctx.bv_or_many(new_args)
            }
            BitVecOp::Xor(args) => {
                let new_args: Vec<_> = (0..args.len())
                    .map(|i| bitvec_child(children, i))
                    .collect::<Result<_, _>>()?;
                ctx.bv_xor_many(new_args)
            }
            BitVecOp::Neg(..) => ctx.neg(bitvec_child(children, 0)?),
            BitVecOp::Add(args) => {
                let new_args: Vec<_> = (0..args.len())
                    .map(|i| bitvec_child(children, i))
                    .collect::<Result<_, _>>()?;
                ctx.add_many(new_args)
            }
            BitVecOp::Sub(..) => ctx.sub(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BitVecOp::Mul(args) => {
                let new_args: Vec<_> = (0..args.len())
                    .map(|i| bitvec_child(children, i))
                    .collect::<Result<_, _>>()?;
                ctx.mul_many(new_args)
            }
            BitVecOp::UDiv(..) => ctx.udiv(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BitVecOp::SDiv(..) => ctx.sdiv(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BitVecOp::URem(..) => ctx.urem(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BitVecOp::SRem(..) => ctx.srem(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BitVecOp::ShL(..) => ctx.shl(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BitVecOp::LShR(..) => ctx.lshr(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BitVecOp::AShR(..) => ctx.ashr(bitvec_child(children, 0)?, bitvec_child(children, 1)?),
            BitVecOp::RotateLeft(..) => {
                ctx.rotate_left(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
            }
            BitVecOp::RotateRight(..) => {
                ctx.rotate_right(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
            }
            BitVecOp::ZeroExt(_, size) => ctx.zero_ext(bitvec_child(children, 0)?, *size),
            BitVecOp::SignExt(_, size) => ctx.sign_ext(bitvec_child(children, 0)?, *size),
            BitVecOp::Extract(_, hi, lo) => ctx.extract(bitvec_child(children, 0)?, *hi, *lo),
            BitVecOp::Concat(args) => {
                let new_args: Vec<_> = (0..args.len())
                    .map(|i| bitvec_child(children, i))
                    .collect::<Result<_, _>>()?;
                ctx.concat(new_args)
            }
            BitVecOp::ByteReverse(..) => ctx.byte_reverse(bitvec_child(children, 0)?),
            BitVecOp::FpToIEEEBV(..) => ctx.fp_to_ieeebv(float_child(children, 0)?),
            BitVecOp::FpToUBV(_, size, fprm) => {
                ctx.fp_to_ubv(float_child(children, 0)?, *size, *fprm)
            }
            BitVecOp::FpToSBV(_, size, fprm) => {
                ctx.fp_to_sbv(float_child(children, 0)?, *size, *fprm)
            }
            BitVecOp::StrLen(..) => ctx.str_len(string_child(children, 0)?),
            BitVecOp::StrIndexOf(..) => ctx.str_index_of(
                string_child(children, 0)?,
                string_child(children, 1)?,
                bitvec_child(children, 2)?,
            ),
            BitVecOp::StrToBV(..) => ctx.str_to_bv(string_child(children, 0)?),
            BitVecOp::ITE(..) => ctx.ite(
                bool_child(children, 0)?,
                bitvec_child(children, 1)?,
                bitvec_child(children, 2)?,
            ),
            BitVecOp::Union(..) => {
                ctx.union(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
            }
            BitVecOp::Intersection(..) => {
                ctx.intersection(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
            }
            BitVecOp::Widen(..) => {
                ctx.widen(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
            }
        }
        .map(DynAst::BitVec),
        DynAst::Float(float_ast) => match float_ast.op() {
            FloatOp::FPS(..) | FloatOp::FPV(..) => Ok(float_ast.clone()),
            FloatOp::FpNeg(..) => ctx.fp_neg(float_child(children, 0)?),
            FloatOp::FpAbs(..) => ctx.fp_abs(float_child(children, 0)?),
            FloatOp::FpAdd(_, _, fprm) => {
                ctx.fp_add(float_child(children, 0)?, float_child(children, 1)?, *fprm)
            }
            FloatOp::FpSub(_, _, fprm) => {
                ctx.fp_sub(float_child(children, 0)?, float_child(children, 1)?, *fprm)
            }
            FloatOp::FpMul(_, _, fprm) => {
                ctx.fp_mul(float_child(children, 0)?, float_child(children, 1)?, *fprm)
            }
            FloatOp::FpDiv(_, _, fprm) => {
                ctx.fp_div(float_child(children, 0)?, float_child(children, 1)?, *fprm)
            }
            FloatOp::FpSqrt(_, fprm) => ctx.fp_sqrt(float_child(children, 0)?, *fprm),
            FloatOp::FpToFp(_, fsort, fprm) => {
                ctx.fp_to_fp(float_child(children, 0)?, *fsort, *fprm)
            }
            FloatOp::FpFP(..) => ctx.fp_fp(
                bitvec_child(children, 0)?,
                bitvec_child(children, 1)?,
                bitvec_child(children, 2)?,
            ),
            FloatOp::BvToFp(_, fsort) => ctx.bv_to_fp(bitvec_child(children, 0)?, *fsort),
            FloatOp::BvToFpSigned(_, fsort, fprm) => {
                ctx.bv_to_fp_signed(bitvec_child(children, 0)?, *fsort, *fprm)
            }
            FloatOp::BvToFpUnsigned(_, fsort, fprm) => {
                ctx.bv_to_fp_unsigned(bitvec_child(children, 0)?, *fsort, *fprm)
            }
            FloatOp::ITE(..) => ctx.ite(
                bool_child(children, 0)?,
                float_child(children, 1)?,
                float_child(children, 2)?,
            ),
        }
        .map(DynAst::Float),
        DynAst::String(string_ast) => match string_ast.op() {
            StringOp::StringS(..) | StringOp::StringV(..) => Ok(string_ast.clone()),
            StringOp::StrConcat(..) => {
                ctx.str_concat(string_child(children, 0)?, string_child(children, 1)?)
            }
            StringOp::StrSubstr(..) => ctx.str_substr(
                string_child(children, 0)?,
                bitvec_child(children, 1)?,
                bitvec_child(children, 2)?,
            ),
            StringOp::StrReplace(..) => ctx.str_replace(
                string_child(children, 0)?,
                string_child(children, 1)?,
                string_child(children, 2)?,
            ),
            StringOp::BVToStr(..) => ctx.bv_to_str(bitvec_child(children, 0)?),
            StringOp::ITE(..) => ctx.ite(
                bool_child(children, 0)?,
                string_child(children, 1)?,
                string_child(children, 2)?,
            ),
        }
        .map(DynAst::String),
    }
}
