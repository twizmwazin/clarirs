use std::collections::BTreeSet;

use num_bigint::BigUint;

use super::factory_support::*;
use crate::error::ClarirsError;
use crate::prelude::*;

pub trait AstFactory<'c>: Sized {
    // Required methods
    fn intern_string(&self, s: impl AsRef<str>) -> InternedString;

    fn make_bool_annotated(
        &'c self,
        op: BooleanOp<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Result<BoolAst<'c>, ClarirsError>;
    fn make_bitvec_annotated(
        &'c self,
        op: BitVecOp<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Result<BitVecAst<'c>, ClarirsError>;
    fn make_float_annotated(
        &'c self,
        op: FloatOp<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Result<FloatAst<'c>, ClarirsError>;
    fn make_string_annotated(
        &'c self,
        op: StringOp<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Result<StringAst<'c>, ClarirsError>;

    // Provided methods

    fn make_bool(&'c self, op: BooleanOp<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool_annotated(op, BTreeSet::new())
    }

    fn make_bitvec(&'c self, op: BitVecOp<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec_annotated(op, BTreeSet::new())
    }

    fn make_float(&'c self, op: FloatOp<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float_annotated(op, BTreeSet::new())
    }

    fn make_string(&'c self, op: StringOp<'c>) -> Result<StringAst<'c>, ClarirsError> {
        self.make_string_annotated(op, BTreeSet::new())
    }

    fn bools<S: AsRef<str>>(&'c self, name: S) -> Result<BoolAst<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make_bool(BooleanOp::BoolS(interned))
    }

    fn boolv(&'c self, value: bool) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::BoolV(value))
    }

    fn bvs<S: AsRef<str>>(&'c self, name: S, width: u32) -> Result<BitVecAst<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make_bitvec(BitVecOp::BVS(interned, width))
    }

    fn bvv(&'c self, value: BitVec) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::BVV(value))
    }

    fn fps<S: AsRef<str>, FS: Into<FSort>>(
        &'c self,
        name: S,
        sort: FS,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make_float(FloatOp::FPS(interned, sort.into()))
    }

    fn fpv<F: Into<Float>>(&'c self, value: F) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FPV(value.into()))
    }

    fn strings<S: AsRef<str>>(&'c self, name: S) -> Result<StringAst<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make_string(StringOp::StringS(interned))
    }

    fn stringv<S: Into<String>>(&'c self, value: S) -> Result<StringAst<'c>, ClarirsError> {
        self.make_string(StringOp::StringV(value.into()))
    }

    fn not<Op: SupportsNot<'c>>(
        &'c self,
        ast: impl IntoOwned<AstRef<'c, Op>>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::not(self, ast)
    }

    fn and(
        &'c self,
        args: impl IntoIterator<Item = BoolAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::And(args.into_iter().collect()))
    }

    fn and2(
        &'c self,
        lhs: impl IntoOwned<BoolAst<'c>>,
        rhs: impl IntoOwned<BoolAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::And(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn or(
        &'c self,
        args: impl IntoIterator<Item = BoolAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::Or(args.into_iter().collect()))
    }

    fn or2(
        &'c self,
        lhs: impl IntoOwned<BoolAst<'c>>,
        rhs: impl IntoOwned<BoolAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::Or(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn xor<Op: SupportsXor<'c>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c, Op>>,
        rhs: impl IntoOwned<AstRef<'c, Op>>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::xor(self, lhs, rhs)
    }

    fn eq_<Op: SupportsEq<'c>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c, Op>>,
        rhs: impl IntoOwned<AstRef<'c, Op>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        Op::eq_(self, lhs, rhs)
    }

    fn neq<Op: SupportsNeq<'c>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c, Op>>,
        rhs: impl IntoOwned<AstRef<'c, Op>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        Op::neq(self, lhs, rhs)
    }

    fn neg(&'c self, ast: impl IntoOwned<BitVecAst<'c>>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::Neg(ast.into_owned()))
    }

    fn bv_and(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::And(lhs.into_owned(), rhs.into_owned()))
    }

    fn bv_or(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::Or(lhs.into_owned(), rhs.into_owned()))
    }

    fn add<Op: SupportsAdd<'c>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c, Op>>,
        rhs: impl IntoOwned<AstRef<'c, Op>>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::add(self, lhs, rhs)
    }

    fn sub<Op: SupportsSub<'c>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c, Op>>,
        rhs: impl IntoOwned<AstRef<'c, Op>>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::sub(self, lhs, rhs)
    }

    fn mul<Op: SupportsMul<'c>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c, Op>>,
        rhs: impl IntoOwned<AstRef<'c, Op>>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::mul(self, lhs, rhs)
    }

    fn udiv<Op: SupportsUDiv<'c>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c, Op>>,
        rhs: impl IntoOwned<AstRef<'c, Op>>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::udiv(self, lhs, rhs)
    }

    fn sdiv<Op: SupportsSDiv<'c>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c, Op>>,
        rhs: impl IntoOwned<AstRef<'c, Op>>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::sdiv(self, lhs, rhs)
    }

    fn urem<Op: SupportsURem<'c>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c, Op>>,
        rhs: impl IntoOwned<AstRef<'c, Op>>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::urem(self, lhs, rhs)
    }

    fn srem<Op: SupportsSRem<'c>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c, Op>>,
        rhs: impl IntoOwned<AstRef<'c, Op>>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::srem(self, lhs, rhs)
    }

    fn shl(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::ShL(lhs.into_owned(), rhs.into_owned()))
    }

    fn ashr(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::AShR(lhs.into_owned(), rhs.into_owned()))
    }

    fn lshr(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::LShR(lhs.into_owned(), rhs.into_owned()))
    }

    fn rotate_left(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::RotateLeft(lhs.into_owned(), rhs.into_owned()))
    }

    fn rotate_right(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::RotateRight(lhs.into_owned(), rhs.into_owned()))
    }

    fn zero_ext(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        width: u32,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::ZeroExt(lhs.into_owned(), width))
    }

    fn sign_ext(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        width: u32,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::SignExt(lhs.into_owned(), width))
    }

    fn extract(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        high: u32,
        low: u32,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::Extract(lhs.into_owned(), high, low))
    }

    fn concat(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::Concat(lhs.into_owned(), rhs.into_owned()))
    }

    fn byte_reverse(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::ByteReverse(lhs.into_owned()))
    }

    fn ult(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::ULT(lhs.into_owned(), rhs.into_owned()))
    }

    fn ule(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::ULE(lhs.into_owned(), rhs.into_owned()))
    }

    fn ugt(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::UGT(lhs.into_owned(), rhs.into_owned()))
    }

    fn uge(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::UGE(lhs.into_owned(), rhs.into_owned()))
    }

    fn slt(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::SLT(lhs.into_owned(), rhs.into_owned()))
    }

    fn sle(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::SLE(lhs.into_owned(), rhs.into_owned()))
    }

    fn sgt(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::SGT(lhs.into_owned(), rhs.into_owned()))
    }

    fn sge(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::SGE(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_to_fp<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        sort: FS,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpToFp(lhs.into_owned(), sort.into(), rm.into()))
    }

    fn bv_to_fp<FS: Into<FSort>>(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        sort: FS,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::BvToFp(lhs.into_owned(), sort.into()))
    }

    fn fp_fp(
        &'c self,
        sign: impl IntoOwned<BitVecAst<'c>>,
        exponent: impl IntoOwned<BitVecAst<'c>>,
        significand: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpFP(
            sign.into_owned(),
            exponent.into_owned(),
            significand.into_owned(),
        ))
    }

    fn bv_to_fp_signed<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        sort: FS,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::BvToFpSigned(
            lhs.into_owned(),
            sort.into(),
            rm.into(),
        ))
    }

    fn bv_to_fp_unsigned<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        sort: FS,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::BvToFpUnsigned(
            lhs.into_owned(),
            sort.into(),
            rm.into(),
        ))
    }

    fn fp_to_ieeebv(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::FpToIEEEBV(lhs.into_owned()))
    }

    fn fp_to_ubv<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        width: u32,
        rm: RM,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::FpToUBV(lhs.into_owned(), width, rm.into()))
    }

    fn fp_to_sbv<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        width: u32,
        rm: RM,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::FpToSBV(lhs.into_owned(), width, rm.into()))
    }

    fn fp_neg(&'c self, lhs: impl IntoOwned<FloatAst<'c>>) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpNeg(lhs.into_owned()))
    }

    fn fp_abs(&'c self, lhs: impl IntoOwned<FloatAst<'c>>) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpAbs(lhs.into_owned()))
    }

    fn fp_add<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpAdd(
            lhs.into_owned(),
            rhs.into_owned(),
            rm.into(),
        ))
    }

    fn fp_sub<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpSub(
            lhs.into_owned(),
            rhs.into_owned(),
            rm.into(),
        ))
    }

    fn fp_mul<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpMul(
            lhs.into_owned(),
            rhs.into_owned(),
            rm.into(),
        ))
    }

    fn fp_div<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpDiv(
            lhs.into_owned(),
            rhs.into_owned(),
            rm.into(),
        ))
    }

    fn fp_sqrt<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make_float(FloatOp::FpSqrt(lhs.into_owned(), rm.into()))
    }

    fn fp_eq(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpEq(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_neq(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpNeq(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_lt(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpLt(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_leq(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpLeq(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_gt(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpGt(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_geq(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpGeq(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_is_nan(&'c self, lhs: impl IntoOwned<FloatAst<'c>>) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpIsNan(lhs.into_owned()))
    }

    fn fp_is_inf(&'c self, lhs: impl IntoOwned<FloatAst<'c>>) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::FpIsInf(lhs.into_owned()))
    }

    fn str_len(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::StrLen(lhs.into_owned()))
    }

    fn str_concat(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
        rhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<StringAst<'c>, ClarirsError> {
        self.make_string(StringOp::StrConcat(lhs.into_owned(), rhs.into_owned()))
    }

    fn str_substr(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
        start: impl IntoOwned<BitVecAst<'c>>,
        size: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<StringAst<'c>, ClarirsError> {
        self.make_string(StringOp::StrSubstr(
            lhs.into_owned(),
            start.into_owned(),
            size.into_owned(),
        ))
    }

    fn str_contains(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
        rhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::StrContains(lhs.into_owned(), rhs.into_owned()))
    }

    fn str_index_of(
        &'c self,
        base: impl IntoOwned<StringAst<'c>>,
        substr: impl IntoOwned<StringAst<'c>>,
        offset: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::StrIndexOf(
            base.into_owned(),
            substr.into_owned(),
            offset.into_owned(),
        ))
    }

    fn str_replace(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
        rhs: impl IntoOwned<StringAst<'c>>,
        start: impl IntoOwned<StringAst<'c>>,
    ) -> Result<StringAst<'c>, ClarirsError> {
        self.make_string(StringOp::StrReplace(
            lhs.into_owned(),
            rhs.into_owned(),
            start.into_owned(),
        ))
    }

    fn str_prefix_of(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
        rhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::StrPrefixOf(lhs.into_owned(), rhs.into_owned()))
    }

    fn str_suffix_of(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
        rhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::StrSuffixOf(lhs.into_owned(), rhs.into_owned()))
    }

    fn str_to_bv(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::StrToBV(lhs.into_owned()))
    }

    fn bv_to_str(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<StringAst<'c>, ClarirsError> {
        self.make_string(StringOp::BVToStr(lhs.into_owned()))
    }

    fn str_is_digit(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::StrIsDigit(lhs.into_owned()))
    }

    fn str_eq(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
        rhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::StrEq(lhs.into_owned(), rhs.into_owned()))
    }

    fn str_neq(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
        rhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make_bool(BooleanOp::StrNeq(lhs.into_owned(), rhs.into_owned()))
    }

    fn ite<Op: SupportsIf<'c>>(
        &'c self,
        cond: impl IntoOwned<AstRef<'c, BooleanOp<'c>>>,
        then: impl IntoOwned<AstRef<'c, Op>>,
        else_: impl IntoOwned<AstRef<'c, Op>>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::ite(self, cond, then, else_)
    }

    fn annotate<Op: SupportsAnnotate<'c>>(
        &'c self,
        ast: impl IntoOwned<AstRef<'c, Op>>,
        annotations: impl IntoIterator<Item = Annotation>,
    ) -> Result<AstRef<'c, Op>, ClarirsError> {
        Op::annotate(ast, annotations)
    }

    fn annotate_dyn(
        &'c self,
        ast: impl IntoOwned<DynAst<'c>>,
        annotations: Vec<Annotation>,
    ) -> Result<DynAst<'c>, ClarirsError> {
        match ast.into_owned() {
            DynAst::Boolean(b) => {
                let annotated = self.annotate(b, annotations.clone())?;
                Ok(DynAst::Boolean(annotated))
            }
            DynAst::BitVec(bv) => {
                let annotated = self.annotate(bv, annotations.clone())?;
                Ok(DynAst::BitVec(annotated))
            }
            DynAst::Float(f) => {
                let annotated = self.annotate(f, annotations.clone())?;
                Ok(DynAst::Float(annotated))
            }
            DynAst::String(s) => {
                let annotated = self.annotate(s, annotations.clone())?;
                Ok(DynAst::String(annotated))
            }
        }
    }

    // VSA methods

    fn si(
        &'c self,
        size: u32,
        stride: BigUint,
        lower_bound: BigUint,
        upper_bound: BigUint,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        let name = format!("SI{size}_{stride}_{lower_bound}_{upper_bound}");
        let interned = self.intern_string(name);
        self.make_bitvec_annotated(
            BitVecOp::BVS(interned, size),
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

    fn esi(&'c self, size: u32) -> Result<BitVecAst<'c>, ClarirsError> {
        let name = format!("ESI{size}");
        let interned = self.intern_string(name);
        self.make_bitvec_annotated(
            BitVecOp::BVS(interned, size),
            BTreeSet::from([Annotation::new(
                AnnotationType::EmptyStridedInterval,
                false,
                false,
            )]),
        )
    }

    fn union(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::Union(lhs.into_owned(), rhs.into_owned()))
    }

    fn intersection(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make_bitvec(BitVecOp::Intersection(lhs.into_owned(), rhs.into_owned()))
    }

    // Helper methods
    fn true_(&'c self) -> Result<BoolAst<'c>, ClarirsError> {
        self.boolv(true)
    }

    fn false_(&'c self) -> Result<BoolAst<'c>, ClarirsError> {
        self.boolv(false)
    }

    fn bvv_prim<T: Into<u64>>(&'c self, value: T) -> Result<BitVecAst<'c>, ClarirsError> {
        self.bvv(BitVec::from_prim(value)?)
    }

    fn bvv_prim_with_size<T: Into<u64>>(
        &'c self,
        value: T,
        length: u32,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.bvv(BitVec::from_prim_with_size(value, length)?)
    }

    fn bvv_from_biguint_with_size(
        &'c self,
        value: &BigUint,
        length: u32,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.bvv(BitVec::from_biguint(value, length)?)
    }

    fn fpv_from_f64(&'c self, value: f64) -> Result<FloatAst<'c>, ClarirsError> {
        self.fpv(Float::from(value))
    }
}
