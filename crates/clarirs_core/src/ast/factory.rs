use std::collections::BTreeSet;

use num_bigint::BigUint;

use crate::error::ClarirsError;
use crate::prelude::*;

pub trait AstFactory<'c>: Sized {
    // Required methods
    fn intern_string(&self, s: impl AsRef<str>) -> InternedString;

    fn make_annotated(
        &'c self,
        op: Op<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError>;

    // Provided methods

    fn make(&'c self, op: Op<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_annotated(op, BTreeSet::new())
    }

    // Backwards-compatible aliases
    fn make_bool(&'c self, op: Op<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make(op)
    }
    fn make_bitvec(&'c self, op: Op<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make(op)
    }
    fn make_float(&'c self, op: Op<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make(op)
    }
    fn make_string(&'c self, op: Op<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make(op)
    }
    fn make_bool_annotated(
        &'c self,
        op: Op<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_annotated(op, annotations)
    }
    fn make_bitvec_annotated(
        &'c self,
        op: Op<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_annotated(op, annotations)
    }
    fn make_float_annotated(
        &'c self,
        op: Op<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_annotated(op, annotations)
    }
    fn make_string_annotated(
        &'c self,
        op: Op<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_annotated(op, annotations)
    }

    fn bools<S: AsRef<str>>(&'c self, name: S) -> Result<BoolAst<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make(Op::BoolS(interned))
    }

    fn boolv(&'c self, value: bool) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::BoolV(value))
    }

    fn bvs<S: AsRef<str>>(&'c self, name: S, width: u32) -> Result<BitVecAst<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make(Op::BVS(interned, width))
    }

    fn bvv(&'c self, value: BitVec) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::BVV(value))
    }

    fn fps<S: AsRef<str>, FS: Into<FSort>>(
        &'c self,
        name: S,
        sort: FS,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make(Op::FPS(interned, sort.into()))
    }

    fn fpv<F: Into<Float>>(&'c self, value: F) -> Result<FloatAst<'c>, ClarirsError> {
        self.make(Op::FPV(value.into()))
    }

    fn strings<S: AsRef<str>>(&'c self, name: S) -> Result<StringAst<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make(Op::StringS(interned))
    }

    fn stringv<S: Into<String>>(&'c self, value: S) -> Result<StringAst<'c>, ClarirsError> {
        self.make(Op::StringV(value.into()))
    }

    fn not(&'c self, ast: impl IntoOwned<AstRef<'c>>) -> Result<AstRef<'c>, ClarirsError> {
        let a = ast.into_owned();
        match a.return_type() {
            AstType::Bool => self.make(Op::Not(a)),
            AstType::BitVec(_) => self.make(Op::BVNot(a)),
            _ => Err(ClarirsError::TypeError("Not requires Bool or BitVec".into())),
        }
    }

    fn and(
        &'c self,
        args: impl IntoIterator<Item = BoolAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::And(args.into_iter().collect()))
    }

    fn and2(
        &'c self,
        lhs: impl IntoOwned<BoolAst<'c>>,
        rhs: impl IntoOwned<BoolAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::And(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn or(
        &'c self,
        args: impl IntoIterator<Item = BoolAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::Or(args.into_iter().collect()))
    }

    fn or2(
        &'c self,
        lhs: impl IntoOwned<BoolAst<'c>>,
        rhs: impl IntoOwned<BoolAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::Or(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn xor(
        &'c self,
        lhs: impl IntoOwned<BoolAst<'c>>,
        rhs: impl IntoOwned<BoolAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::Xor(lhs.into_owned(), rhs.into_owned()))
    }

    fn eq_(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        let l = lhs.into_owned();
        let r = rhs.into_owned();
        match l.return_type() {
            AstType::Bool => self.make(Op::BoolEq(l, r)),
            AstType::BitVec(_) => self.make(Op::Eq(l, r)),
            AstType::Float(_) => self.make(Op::FpEq(l, r)),
            AstType::String => self.make(Op::StrEq(l, r)),
        }
    }

    fn neq(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        let l = lhs.into_owned();
        let r = rhs.into_owned();
        match l.return_type() {
            AstType::Bool => self.make(Op::BoolNeq(l, r)),
            AstType::BitVec(_) => self.make(Op::Neq(l, r)),
            AstType::Float(_) => self.make(Op::FpNeq(l, r)),
            AstType::String => self.make(Op::StrNeq(l, r)),
        }
    }

    fn neg(&'c self, ast: impl IntoOwned<BitVecAst<'c>>) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::Neg(ast.into_owned()))
    }

    fn bv_and(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::BVAnd(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn bv_and_many(
        &'c self,
        args: impl IntoIterator<Item = BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::BVAnd(args.into_iter().collect()))
    }

    fn bv_or(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::BVOr(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn bv_or_many(
        &'c self,
        args: impl IntoIterator<Item = BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::BVOr(args.into_iter().collect()))
    }

    fn bv_xor(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::BVXor(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn bv_xor_many(
        &'c self,
        args: impl IntoIterator<Item = BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::BVXor(args.into_iter().collect()))
    }

    fn add(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::Add(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn add_many(
        &'c self,
        args: impl IntoIterator<Item = BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::Add(args.into_iter().collect()))
    }

    fn mul(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::Mul(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn mul_many(
        &'c self,
        args: impl IntoIterator<Item = BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::Mul(args.into_iter().collect()))
    }

    fn sub(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::Sub(lhs.into_owned(), rhs.into_owned()))
    }

    fn udiv(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::UDiv(lhs.into_owned(), rhs.into_owned()))
    }

    fn sdiv(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::SDiv(lhs.into_owned(), rhs.into_owned()))
    }

    fn urem(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::URem(lhs.into_owned(), rhs.into_owned()))
    }

    fn srem(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::SRem(lhs.into_owned(), rhs.into_owned()))
    }

    fn shl(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::ShL(lhs.into_owned(), rhs.into_owned()))
    }

    fn ashr(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::AShR(lhs.into_owned(), rhs.into_owned()))
    }

    fn lshr(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::LShR(lhs.into_owned(), rhs.into_owned()))
    }

    fn rotate_left(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::RotateLeft(lhs.into_owned(), rhs.into_owned()))
    }

    fn rotate_right(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::RotateRight(lhs.into_owned(), rhs.into_owned()))
    }

    fn zero_ext(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        width: u32,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::ZeroExt(lhs.into_owned(), width))
    }

    fn sign_ext(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        width: u32,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::SignExt(lhs.into_owned(), width))
    }

    fn extract(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        high: u32,
        low: u32,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::Extract(lhs.into_owned(), high, low))
    }

    fn concat(
        &'c self,
        args: impl IntoIterator<Item = BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        let args: Vec<BitVecAst<'c>> = args.into_iter().collect();
        if args.is_empty() {
            return Err(ClarirsError::InvalidArguments(
                "Concat requires at least one argument".to_string(),
            ));
        }
        self.make(Op::Concat(args))
    }

    fn concat2(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.concat([lhs.into_owned(), rhs.into_owned()])
    }

    fn byte_reverse(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::ByteReverse(lhs.into_owned()))
    }

    fn ult(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::ULT(lhs.into_owned(), rhs.into_owned()))
    }

    fn ule(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::ULE(lhs.into_owned(), rhs.into_owned()))
    }

    fn ugt(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::UGT(lhs.into_owned(), rhs.into_owned()))
    }

    fn uge(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::UGE(lhs.into_owned(), rhs.into_owned()))
    }

    fn slt(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::SLT(lhs.into_owned(), rhs.into_owned()))
    }

    fn sle(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::SLE(lhs.into_owned(), rhs.into_owned()))
    }

    fn sgt(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::SGT(lhs.into_owned(), rhs.into_owned()))
    }

    fn sge(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::SGE(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_to_fp<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        sort: FS,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make(Op::FpToFp(lhs.into_owned(), sort.into(), rm.into()))
    }

    fn bv_to_fp<FS: Into<FSort>>(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        sort: FS,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make(Op::BvToFp(lhs.into_owned(), sort.into()))
    }

    fn fp_fp(
        &'c self,
        sign: impl IntoOwned<BitVecAst<'c>>,
        exponent: impl IntoOwned<BitVecAst<'c>>,
        significand: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make(Op::FpFP(
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
        self.make(Op::BvToFpSigned(lhs.into_owned(), sort.into(), rm.into()))
    }

    fn bv_to_fp_unsigned<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        sort: FS,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make(Op::BvToFpUnsigned(
            lhs.into_owned(),
            sort.into(),
            rm.into(),
        ))
    }

    fn fp_to_ieeebv(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::FpToIEEEBV(lhs.into_owned()))
    }

    fn fp_to_ubv<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        width: u32,
        rm: RM,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::FpToUBV(lhs.into_owned(), width, rm.into()))
    }

    fn fp_to_sbv<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        width: u32,
        rm: RM,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::FpToSBV(lhs.into_owned(), width, rm.into()))
    }

    fn fp_neg(&'c self, lhs: impl IntoOwned<FloatAst<'c>>) -> Result<FloatAst<'c>, ClarirsError> {
        self.make(Op::FpNeg(lhs.into_owned()))
    }

    fn fp_abs(&'c self, lhs: impl IntoOwned<FloatAst<'c>>) -> Result<FloatAst<'c>, ClarirsError> {
        self.make(Op::FpAbs(lhs.into_owned()))
    }

    fn fp_add<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make(Op::FpAdd(lhs.into_owned(), rhs.into_owned(), rm.into()))
    }

    fn fp_sub<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make(Op::FpSub(lhs.into_owned(), rhs.into_owned(), rm.into()))
    }

    fn fp_mul<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make(Op::FpMul(lhs.into_owned(), rhs.into_owned(), rm.into()))
    }

    fn fp_div<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make(Op::FpDiv(lhs.into_owned(), rhs.into_owned(), rm.into()))
    }

    fn fp_sqrt<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rm: RM,
    ) -> Result<FloatAst<'c>, ClarirsError> {
        self.make(Op::FpSqrt(lhs.into_owned(), rm.into()))
    }

    fn fp_eq(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::FpEq(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_neq(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::FpNeq(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_lt(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::FpLt(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_leq(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::FpLeq(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_gt(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::FpGt(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_geq(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
        rhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::FpGeq(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_is_nan(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::FpIsNan(lhs.into_owned()))
    }

    fn fp_is_inf(
        &'c self,
        lhs: impl IntoOwned<FloatAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::FpIsInf(lhs.into_owned()))
    }

    fn str_len(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::StrLen(lhs.into_owned()))
    }

    fn str_concat(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
        rhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<StringAst<'c>, ClarirsError> {
        self.make(Op::StrConcat(lhs.into_owned(), rhs.into_owned()))
    }

    fn str_substr(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
        start: impl IntoOwned<BitVecAst<'c>>,
        size: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<StringAst<'c>, ClarirsError> {
        self.make(Op::StrSubstr(
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
        self.make(Op::StrContains(lhs.into_owned(), rhs.into_owned()))
    }

    fn str_index_of(
        &'c self,
        base: impl IntoOwned<StringAst<'c>>,
        substr: impl IntoOwned<StringAst<'c>>,
        offset: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::StrIndexOf(
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
        self.make(Op::StrReplace(
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
        self.make(Op::StrPrefixOf(lhs.into_owned(), rhs.into_owned()))
    }

    fn str_suffix_of(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
        rhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::StrSuffixOf(lhs.into_owned(), rhs.into_owned()))
    }

    fn str_to_bv(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::StrToBV(lhs.into_owned()))
    }

    fn bv_to_str(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<StringAst<'c>, ClarirsError> {
        self.make(Op::BVToStr(lhs.into_owned()))
    }

    fn str_is_digit(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::StrIsDigit(lhs.into_owned()))
    }

    fn str_eq(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
        rhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::StrEq(lhs.into_owned(), rhs.into_owned()))
    }

    fn str_neq(
        &'c self,
        lhs: impl IntoOwned<StringAst<'c>>,
        rhs: impl IntoOwned<StringAst<'c>>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        self.make(Op::StrNeq(lhs.into_owned(), rhs.into_owned()))
    }

    fn ite(
        &'c self,
        cond: impl IntoOwned<BoolAst<'c>>,
        then: impl IntoOwned<AstRef<'c>>,
        else_: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make(Op::ITE(cond.into_owned(), then.into_owned(), else_.into_owned()))
    }

    fn annotate(
        &'c self,
        ast: impl IntoOwned<AstRef<'c>>,
        annotations: impl IntoIterator<Item = Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        let ast_owned = ast.into_owned();
        let all_annotations = ast_owned
            .annotations()
            .iter()
            .cloned()
            .chain(annotations)
            .collect();
        self.make_annotated(ast_owned.op().clone(), all_annotations)
    }

    fn annotate_dyn(
        &'c self,
        ast: impl IntoOwned<AstRef<'c>>,
        annotations: Vec<Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.annotate(ast, annotations)
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
        self.make_annotated(
            Op::BVS(interned, size),
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
        self.make_annotated(
            Op::BVS(interned, size),
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
        self.make(Op::Union(lhs.into_owned(), rhs.into_owned()))
    }

    fn intersection(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::Intersection(lhs.into_owned(), rhs.into_owned()))
    }

    fn widen(
        &'c self,
        lhs: impl IntoOwned<BitVecAst<'c>>,
        rhs: impl IntoOwned<BitVecAst<'c>>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        self.make(Op::Widen(lhs.into_owned(), rhs.into_owned()))
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
