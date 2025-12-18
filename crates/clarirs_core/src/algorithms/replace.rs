use std::mem::discriminant;

use crate::{
    algorithms::{
        post_order::{bitvec_child, bool_child, float_child, string_child},
        walk_post_order,
    },
    ast::{bitvec::BitVecOpExt, float::FloatOpExt},
    prelude::*,
};

pub trait Replace<'c, T>: Sized {
    fn replace(&self, from: &T, to: &T) -> Result<Self, ClarirsError>;
}

impl<'c, T: Clone + Into<DynAst<'c>>> Replace<'c, T> for DynAst<'c> {
    fn replace(&self, from: &T, to: &T) -> Result<Self, ClarirsError> {
        let from = from.clone().into();
        let to = to.clone().into();

        if discriminant(&from) != discriminant(&to) {
            return Err(ClarirsError::TypeError(
                "Replace types must match!".to_string(),
            ));
        }
        if let Some(from_bv) = from.as_bitvec() {
            if let Some(to_bv) = to.as_bitvec() {
                if from_bv.size() != to_bv.size() {
                    return Err(ClarirsError::TypeError(
                        "BitVec sizes must match for replacement!".to_string(),
                    ));
                }
            }
        }
        if let Some(from_fp) = from.as_float() {
            if let Some(to_fp) = to.as_float() {
                if from_fp.sort() != to_fp.sort() {
                    return Err(ClarirsError::TypeError(
                        "Float sorts must match for replacement!".to_string(),
                    ));
                }
            }
        }

        let ctx = self.context();
        walk_post_order(
            self.clone(),
            |ast, children| match &ast {
                _ if ast == from => Ok(to.clone()),
                DynAst::Boolean(bool_ast) => match bool_ast.op() {
                    BooleanOp::BoolS(..) | BooleanOp::BoolV(..) => Ok(bool_ast.clone()),
                    BooleanOp::Not(..) => ctx.not(bool_child(children, 0)?),
                    BooleanOp::And(..) => {
                        ctx.and(bool_child(children, 0)?, bool_child(children, 1)?)
                    }
                    BooleanOp::Or(..) => ctx.or(bool_child(children, 0)?, bool_child(children, 1)?),
                    BooleanOp::Xor(..) => {
                        ctx.xor(bool_child(children, 0)?, bool_child(children, 1)?)
                    }
                    BooleanOp::BoolEq(..) => {
                        ctx.eq_(bool_child(children, 0)?, bool_child(children, 1)?)
                    }
                    BooleanOp::BoolNeq(..) => {
                        ctx.neq(bool_child(children, 0)?, bool_child(children, 1)?)
                    }
                    BooleanOp::Eq(..) => {
                        ctx.eq_(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BooleanOp::Neq(..) => {
                        ctx.neq(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BooleanOp::ULT(..) => {
                        ctx.ult(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BooleanOp::ULE(..) => {
                        ctx.ule(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BooleanOp::UGT(..) => {
                        ctx.ugt(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BooleanOp::UGE(..) => {
                        ctx.uge(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BooleanOp::SLT(..) => {
                        ctx.slt(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BooleanOp::SLE(..) => {
                        ctx.sle(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BooleanOp::SGT(..) => {
                        ctx.sgt(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BooleanOp::SGE(..) => {
                        ctx.sge(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BooleanOp::FpEq(..) => {
                        ctx.fp_eq(float_child(children, 0)?, float_child(children, 1)?)
                    }
                    BooleanOp::FpNeq(..) => {
                        ctx.fp_neq(float_child(children, 0)?, float_child(children, 1)?)
                    }
                    BooleanOp::FpLt(..) => {
                        ctx.fp_lt(float_child(children, 0)?, float_child(children, 1)?)
                    }
                    BooleanOp::FpLeq(..) => {
                        ctx.fp_leq(float_child(children, 0)?, float_child(children, 1)?)
                    }
                    BooleanOp::FpGt(..) => {
                        ctx.fp_gt(float_child(children, 0)?, float_child(children, 1)?)
                    }
                    BooleanOp::FpGeq(..) => {
                        ctx.fp_geq(float_child(children, 0)?, float_child(children, 1)?)
                    }
                    BooleanOp::FpIsNan(..) => ctx.fp_is_nan(float_child(children, 0)?),
                    BooleanOp::FpIsInf(..) => ctx.fp_is_inf(float_child(children, 0)?),
                    BooleanOp::StrContains(..) => {
                        ctx.strcontains(string_child(children, 0)?, string_child(children, 1)?)
                    }
                    BooleanOp::StrPrefixOf(..) => {
                        ctx.strprefixof(string_child(children, 0)?, string_child(children, 1)?)
                    }
                    BooleanOp::StrSuffixOf(..) => {
                        ctx.strsuffixof(string_child(children, 0)?, string_child(children, 1)?)
                    }
                    BooleanOp::StrIsDigit(..) => ctx.strisdigit(string_child(children, 0)?),
                    BooleanOp::StrEq(..) => {
                        ctx.streq(string_child(children, 0)?, string_child(children, 1)?)
                    }
                    BooleanOp::StrNeq(..) => {
                        ctx.strneq(string_child(children, 0)?, string_child(children, 1)?)
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
                    BitVecOp::And(..) => {
                        ctx.and(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::Or(..) => {
                        ctx.or(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::Xor(..) => {
                        ctx.xor(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::Neg(..) => ctx.neg(bitvec_child(children, 0)?),
                    BitVecOp::Add(..) => {
                        ctx.add(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::Sub(..) => {
                        ctx.sub(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::Mul(..) => {
                        ctx.mul(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::UDiv(..) => {
                        ctx.udiv(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::SDiv(..) => {
                        ctx.sdiv(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::URem(..) => {
                        ctx.urem(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::SRem(..) => {
                        ctx.srem(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::ShL(..) => {
                        ctx.shl(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::LShR(..) => {
                        ctx.lshr(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::AShR(..) => {
                        ctx.ashr(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::RotateLeft(..) => {
                        ctx.rotate_left(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::RotateRight(..) => {
                        ctx.rotate_right(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::ZeroExt(_, size) => ctx.zero_ext(bitvec_child(children, 0)?, *size),
                    BitVecOp::SignExt(_, size) => ctx.sign_ext(bitvec_child(children, 0)?, *size),
                    BitVecOp::Extract(_, hi, lo) => {
                        ctx.extract(bitvec_child(children, 0)?, *hi, *lo)
                    }
                    BitVecOp::Concat(..) => {
                        ctx.concat(bitvec_child(children, 0)?, bitvec_child(children, 1)?)
                    }
                    BitVecOp::ByteReverse(..) => ctx.byte_reverse(bitvec_child(children, 0)?),
                    BitVecOp::FpToIEEEBV(..) => ctx.fp_to_ieeebv(float_child(children, 0)?),
                    BitVecOp::FpToUBV(_, size, fprm) => {
                        ctx.fp_to_ubv(float_child(children, 0)?, *size, *fprm)
                    }
                    BitVecOp::FpToSBV(_, size, fprm) => {
                        ctx.fp_to_sbv(float_child(children, 0)?, *size, *fprm)
                    }
                    BitVecOp::StrLen(..) => ctx.strlen(string_child(children, 0)?),
                    BitVecOp::StrIndexOf(..) => ctx.strindexof(
                        string_child(children, 0)?,
                        string_child(children, 1)?,
                        bitvec_child(children, 2)?,
                    ),
                    BitVecOp::StrToBV(..) => ctx.strtobv(string_child(children, 0)?),
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
                        ctx.strconcat(string_child(children, 0)?, string_child(children, 1)?)
                    }
                    StringOp::StrSubstr(..) => ctx.strsubstr(
                        string_child(children, 0)?,
                        bitvec_child(children, 1)?,
                        bitvec_child(children, 2)?,
                    ),
                    StringOp::StrReplace(..) => ctx.strreplace(
                        string_child(children, 0)?,
                        string_child(children, 1)?,
                        string_child(children, 2)?,
                    ),
                    StringOp::BVToStr(..) => ctx.bvtostr(bitvec_child(children, 0)?),
                    StringOp::ITE(..) => ctx.ite(
                        bool_child(children, 0)?,
                        string_child(children, 1)?,
                        string_child(children, 2)?,
                    ),
                }
                .map(DynAst::String),
            },
            &(),
        )
    }
}

impl<'c, T: Clone + Into<DynAst<'c>>> Replace<'c, T> for BoolAst<'c> {
    fn replace(&self, from: &T, to: &T) -> Result<Self, ClarirsError> {
        DynAst::Boolean(self.clone())
            .replace(from, to)
            .and_then(|replaced| {
                replaced.into_bool().ok_or(ClarirsError::TypeError(
                    "Expected Boolean after replacement".to_string(),
                ))
            })
    }
}

impl<'c, T: Clone + Into<DynAst<'c>>> Replace<'c, T> for BitVecAst<'c> {
    fn replace(&self, from: &T, to: &T) -> Result<Self, ClarirsError> {
        DynAst::BitVec(self.clone())
            .replace(from, to)
            .and_then(|replaced| {
                replaced.into_bitvec().ok_or(ClarirsError::TypeError(
                    "Expected BitVec after replacement".to_string(),
                ))
            })
    }
}

impl<'c, T: Clone + Into<DynAst<'c>>> Replace<'c, T> for FloatAst<'c> {
    fn replace(&self, from: &T, to: &T) -> Result<Self, ClarirsError> {
        DynAst::Float(self.clone())
            .replace(from, to)
            .and_then(|replaced| {
                replaced.into_float().ok_or(ClarirsError::TypeError(
                    "Expected Float after replacement".to_string(),
                ))
            })
    }
}

impl<'c, T: Clone + Into<DynAst<'c>>> Replace<'c, T> for StringAst<'c> {
    fn replace(&self, from: &T, to: &T) -> Result<Self, ClarirsError> {
        DynAst::String(self.clone())
            .replace(from, to)
            .and_then(|replaced| {
                replaced.into_string().ok_or(ClarirsError::TypeError(
                    "Expected String after replacement".to_string(),
                ))
            })
    }
}
