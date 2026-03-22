use std::collections::BTreeSet;

use num_bigint::BigUint;

use crate::error::ClarirsError;
use crate::prelude::*;

pub trait AstFactory<'c>: Sized {
    // Required methods
    fn intern_string(&self, s: impl AsRef<str>) -> InternedString;

    fn make_ast_annotated(
        &'c self,
        op: AstOp<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError>;

    // Provided methods

    fn make_ast(&'c self, op: AstOp<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast_annotated(op, BTreeSet::new())
    }

    fn bools<S: AsRef<str>>(&'c self, name: S) -> Result<AstRef<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make_ast(AstOp::BoolS(interned))
    }

    fn boolv(&'c self, value: bool) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::BoolV(value))
    }

    fn bvs<S: AsRef<str>>(&'c self, name: S, width: u32) -> Result<AstRef<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make_ast(AstOp::BVS(interned, width))
    }

    fn bvv(&'c self, value: BitVec) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::BVV(value))
    }

    fn fps<S: AsRef<str>, FS: Into<FSort>>(
        &'c self,
        name: S,
        sort: FS,
    ) -> Result<AstRef<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make_ast(AstOp::FPS(interned, sort.into()))
    }

    fn fpv<F: Into<Float>>(&'c self, value: F) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FPV(value.into()))
    }

    fn strings<S: AsRef<str>>(&'c self, name: S) -> Result<AstRef<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make_ast(AstOp::StringS(interned))
    }

    fn stringv<S: Into<String>>(&'c self, value: S) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StringV(value.into()))
    }

    fn not(&'c self, ast: impl IntoAstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Not(ast.into_ast_ref()))
    }

    fn and(
        &'c self,
        args: impl IntoIterator<Item = AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::And(args.into_iter().collect()))
    }

    fn and2(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::And(vec![lhs.into_ast_ref(), rhs.into_ast_ref()]))
    }

    fn or(
        &'c self,
        args: impl IntoIterator<Item = AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Or(args.into_iter().collect()))
    }

    fn or2(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Or(vec![lhs.into_ast_ref(), rhs.into_ast_ref()]))
    }

    fn xor(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Xor(vec![lhs.into_ast_ref(), rhs.into_ast_ref()]))
    }

    fn eq_(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Eq(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn neq(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Neq(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn neg(&'c self, ast: impl IntoAstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Neg(ast.into_ast_ref()))
    }

    fn bv_and(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::And(vec![lhs.into_ast_ref(), rhs.into_ast_ref()]))
    }

    fn bv_and_many(
        &'c self,
        args: impl IntoIterator<Item = AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::And(args.into_iter().collect()))
    }

    fn bv_or(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Or(vec![lhs.into_ast_ref(), rhs.into_ast_ref()]))
    }

    fn bv_or_many(
        &'c self,
        args: impl IntoIterator<Item = AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Or(args.into_iter().collect()))
    }

    fn bv_xor(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Xor(vec![lhs.into_ast_ref(), rhs.into_ast_ref()]))
    }

    fn bv_xor_many(
        &'c self,
        args: impl IntoIterator<Item = AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Xor(args.into_iter().collect()))
    }

    fn add(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Add(vec![lhs.into_ast_ref(), rhs.into_ast_ref()]))
    }

    fn add_many(
        &'c self,
        args: impl IntoIterator<Item = AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Add(args.into_iter().collect()))
    }

    fn mul(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Mul(vec![lhs.into_ast_ref(), rhs.into_ast_ref()]))
    }

    fn mul_many(
        &'c self,
        args: impl IntoIterator<Item = AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Mul(args.into_iter().collect()))
    }

    fn sub(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Sub(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn udiv(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::UDiv(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn sdiv(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::SDiv(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn urem(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::URem(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn srem(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::SRem(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn shl(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::ShL(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn ashr(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::AShR(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn lshr(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::LShR(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn rotate_left(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::RotateLeft(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn rotate_right(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::RotateRight(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn zero_ext(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        width: u32,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::ZeroExt(lhs.into_ast_ref(), width))
    }

    fn sign_ext(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        width: u32,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::SignExt(lhs.into_ast_ref(), width))
    }

    fn extract(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        high: u32,
        low: u32,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Extract(lhs.into_ast_ref(), high, low))
    }

    fn concat(
        &'c self,
        args: impl IntoIterator<Item = AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        let args: Vec<AstRef<'c>> = args.into_iter().collect();
        if args.is_empty() {
            return Err(ClarirsError::InvalidArguments(
                "Concat requires at least one argument".to_string(),
            ));
        }
        self.make_ast(AstOp::Concat(args))
    }

    fn concat2(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.concat([lhs.into_ast_ref(), rhs.into_ast_ref()])
    }

    fn byte_reverse(&'c self, lhs: impl IntoAstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::ByteReverse(lhs.into_ast_ref()))
    }

    fn ult(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::ULT(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn ule(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::ULE(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn ugt(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::UGT(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn uge(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::UGE(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn slt(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::SLT(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn sle(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::SLE(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn sgt(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::SGT(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn sge(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::SGE(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn fp_to_fp<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        sort: FS,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpToFp(lhs.into_ast_ref(), sort.into(), rm.into()))
    }

    fn bv_to_fp<FS: Into<FSort>>(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        sort: FS,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::BvToFp(lhs.into_ast_ref(), sort.into()))
    }

    fn fp_fp(
        &'c self,
        sign: impl IntoAstRef<'c>,
        exponent: impl IntoAstRef<'c>,
        significand: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpFP(
            sign.into_ast_ref(),
            exponent.into_ast_ref(),
            significand.into_ast_ref(),
        ))
    }

    fn bv_to_fp_signed<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        sort: FS,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::BvToFpSigned(
            lhs.into_ast_ref(),
            sort.into(),
            rm.into(),
        ))
    }

    fn bv_to_fp_unsigned<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        sort: FS,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::BvToFpUnsigned(
            lhs.into_ast_ref(),
            sort.into(),
            rm.into(),
        ))
    }

    fn fp_to_ieeebv(&'c self, lhs: impl IntoAstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpToIEEEBV(lhs.into_ast_ref()))
    }

    fn fp_to_ubv<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        width: u32,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpToUBV(lhs.into_ast_ref(), width, rm.into()))
    }

    fn fp_to_sbv<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        width: u32,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpToSBV(lhs.into_ast_ref(), width, rm.into()))
    }

    fn fp_neg(&'c self, lhs: impl IntoAstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpNeg(lhs.into_ast_ref()))
    }

    fn fp_abs(&'c self, lhs: impl IntoAstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpAbs(lhs.into_ast_ref()))
    }

    fn fp_add<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpAdd(
            lhs.into_ast_ref(),
            rhs.into_ast_ref(),
            rm.into(),
        ))
    }

    fn fp_sub<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpSub(
            lhs.into_ast_ref(),
            rhs.into_ast_ref(),
            rm.into(),
        ))
    }

    fn fp_mul<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpMul(
            lhs.into_ast_ref(),
            rhs.into_ast_ref(),
            rm.into(),
        ))
    }

    fn fp_div<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpDiv(
            lhs.into_ast_ref(),
            rhs.into_ast_ref(),
            rm.into(),
        ))
    }

    fn fp_sqrt<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpSqrt(lhs.into_ast_ref(), rm.into()))
    }

    fn fp_eq(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Eq(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn fp_neq(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Neq(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn fp_lt(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpLt(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn fp_leq(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpLeq(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn fp_gt(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpGt(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn fp_geq(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpGeq(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn fp_is_nan(&'c self, lhs: impl IntoAstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpIsNan(lhs.into_ast_ref()))
    }

    fn fp_is_inf(&'c self, lhs: impl IntoAstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::FpIsInf(lhs.into_ast_ref()))
    }

    fn str_len(&'c self, lhs: impl IntoAstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrLen(lhs.into_ast_ref()))
    }

    fn str_concat(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrConcat(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn str_substr(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        start: impl IntoAstRef<'c>,
        size: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrSubstr(
            lhs.into_ast_ref(),
            start.into_ast_ref(),
            size.into_ast_ref(),
        ))
    }

    fn str_contains(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrContains(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn str_index_of(
        &'c self,
        base: impl IntoAstRef<'c>,
        substr: impl IntoAstRef<'c>,
        offset: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrIndexOf(
            base.into_ast_ref(),
            substr.into_ast_ref(),
            offset.into_ast_ref(),
        ))
    }

    fn str_replace(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
        start: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrReplace(
            lhs.into_ast_ref(),
            rhs.into_ast_ref(),
            start.into_ast_ref(),
        ))
    }

    fn str_prefix_of(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrPrefixOf(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn str_suffix_of(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrSuffixOf(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn str_to_bv(&'c self, lhs: impl IntoAstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrToBV(lhs.into_ast_ref()))
    }

    fn bv_to_str(&'c self, lhs: impl IntoAstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::BVToStr(lhs.into_ast_ref()))
    }

    fn str_is_digit(&'c self, lhs: impl IntoAstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::StrIsDigit(lhs.into_ast_ref()))
    }

    fn str_eq(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Eq(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn str_neq(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Neq(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn ite(
        &'c self,
        cond: impl IntoAstRef<'c>,
        then: impl IntoAstRef<'c>,
        else_: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::If(
            cond.into_ast_ref(),
            then.into_ast_ref(),
            else_.into_ast_ref(),
        ))
    }

    fn annotate(
        &'c self,
        ast: impl IntoAstRef<'c>,
        annotations: impl IntoIterator<Item = Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        let ast = ast.into_ast_ref();
        let new_annotations: BTreeSet<Annotation> = ast
            .annotations()
            .iter()
            .cloned()
            .chain(annotations)
            .collect();
        self.make_ast_annotated(ast.op().clone(), new_annotations)
    }

    // VSA methods

    fn si(
        &'c self,
        size: u32,
        stride: BigUint,
        lower_bound: BigUint,
        upper_bound: BigUint,
    ) -> Result<AstRef<'c>, ClarirsError> {
        let name = format!("SI{size}_{stride}_{lower_bound}_{upper_bound}");
        let interned = self.intern_string(name);
        self.make_ast_annotated(
            AstOp::BVS(interned, size),
            BTreeSet::from([Annotation::new(
                AnnotationType::StridedInterval {
                    stride,
                    lower_bound,
                    upper_bound,
                },
                false,
                false,
            )]),
        )
    }

    fn esi(&'c self, size: u32) -> Result<AstRef<'c>, ClarirsError> {
        let name = format!("ESI{size}");
        let interned = self.intern_string(name);
        self.make_ast_annotated(
            AstOp::BVS(interned, size),
            BTreeSet::from([Annotation::new(
                AnnotationType::EmptyStridedInterval,
                false,
                false,
            )]),
        )
    }

    fn union(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Union(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn intersection(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Intersection(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    fn widen(
        &'c self,
        lhs: impl IntoAstRef<'c>,
        rhs: impl IntoAstRef<'c>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_ast(AstOp::Widen(lhs.into_ast_ref(), rhs.into_ast_ref()))
    }

    // Helper methods
    fn true_(&'c self) -> Result<AstRef<'c>, ClarirsError> {
        self.boolv(true)
    }

    fn false_(&'c self) -> Result<AstRef<'c>, ClarirsError> {
        self.boolv(false)
    }

    fn bvv_prim<T: Into<u64>>(&'c self, value: T) -> Result<AstRef<'c>, ClarirsError> {
        self.bvv(BitVec::from_prim(value)?)
    }

    fn bvv_prim_with_size<T: Into<u64>>(
        &'c self,
        value: T,
        length: u32,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.bvv(BitVec::from_prim_with_size(value, length)?)
    }

    fn bvv_from_biguint_with_size(
        &'c self,
        value: &BigUint,
        length: u32,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.bvv(BitVec::from_biguint(value, length)?)
    }

    fn fpv_from_f64(&'c self, value: f64) -> Result<AstRef<'c>, ClarirsError> {
        self.fpv(Float::from(value))
    }
}
