use std::collections::BTreeSet;

use num_bigint::BigUint;

use crate::ast::op::{AstOp, AstType};
use crate::error::ClarirsError;
use crate::prelude::*;

pub trait AstFactory<'c>: Sized {
    // Required methods
    fn intern_string(&self, s: impl AsRef<str>) -> InternedString;

    /// The single node constructor. All other `make_*` helpers delegate here;
    /// the node's type is inferred from the operation.
    fn make_annotated(
        &'c self,
        op: AstOp<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError>;

    // Provided methods

    fn make(&'c self, op: AstOp<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_annotated(op, BTreeSet::new())
    }

    // Sort-specific aliases kept for readability at call sites. They are all
    // the same operation; the resulting node's type is inferred.
    fn make_bool(&'c self, op: AstOp<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make(op)
    }
    fn make_bool_annotated(
        &'c self,
        op: AstOp<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_annotated(op, annotations)
    }

    fn make_bitvec(&'c self, op: AstOp<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make(op)
    }
    fn make_bitvec_annotated(
        &'c self,
        op: AstOp<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_annotated(op, annotations)
    }

    fn make_float(&'c self, op: AstOp<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make(op)
    }
    fn make_float_annotated(
        &'c self,
        op: AstOp<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_annotated(op, annotations)
    }

    fn make_string(&'c self, op: AstOp<'c>) -> Result<AstRef<'c>, ClarirsError> {
        self.make(op)
    }
    fn make_string_annotated(
        &'c self,
        op: AstOp<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_annotated(op, annotations)
    }

    fn bools<S: AsRef<str>>(&'c self, name: S) -> Result<AstRef<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make_bool(AstOp::BoolS(interned))
    }

    fn boolv(&'c self, value: bool) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::BoolV(value))
    }

    fn bvs<S: AsRef<str>>(&'c self, name: S, width: u32) -> Result<AstRef<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make_bitvec(AstOp::BVS(interned, width))
    }

    fn bvv(&'c self, value: BitVec) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::BVV(value))
    }

    fn fps<S: AsRef<str>, FS: Into<FSort>>(
        &'c self,
        name: S,
        sort: FS,
    ) -> Result<AstRef<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make_float(AstOp::FPS(interned, sort.into()))
    }

    fn fpv<F: Into<Float>>(&'c self, value: F) -> Result<AstRef<'c>, ClarirsError> {
        self.make_float(AstOp::FPV(value.into()))
    }

    fn strings<S: AsRef<str>>(&'c self, name: S) -> Result<AstRef<'c>, ClarirsError> {
        let interned = self.intern_string(name);
        self.make_string(AstOp::StringS(interned))
    }

    fn stringv<S: Into<String>>(&'c self, value: S) -> Result<AstRef<'c>, ClarirsError> {
        self.make_string(AstOp::StringV(value.into()))
    }

    /// Logical/bitwise negation. Requires a boolean or bitvector operand.
    fn not(&'c self, ast: impl IntoOwned<AstRef<'c>>) -> Result<AstRef<'c>, ClarirsError> {
        let ast = ast.into_owned();
        match ast.ty() {
            AstType::Bool | AstType::BitVec(_) => self.make(AstOp::Not(ast)),
            ty => Err(ClarirsError::TypeError(format!(
                "not() requires a boolean or bitvector operand, got {ty:?}"
            ))),
        }
    }

    fn and(
        &'c self,
        args: impl IntoIterator<Item = AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::And(args.into_iter().collect()))
    }

    fn and2(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::And(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn or(
        &'c self,
        args: impl IntoIterator<Item = AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::Or(args.into_iter().collect()))
    }

    fn or2(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::Or(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn xor(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::BoolXor(lhs.into_owned(), rhs.into_owned()))
    }

    /// Structural equality. The operands must have the same sort; the
    /// appropriate equality operation is chosen based on that sort.
    fn eq_(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        let lhs = lhs.into_owned();
        let rhs = rhs.into_owned();
        if !lhs.check_same_sort(&rhs) {
            return Err(ClarirsError::TypeError(format!(
                "Sort mismatch in eq: {lhs:?} and {rhs:?}"
            )));
        }
        self.make_bool(AstOp::Eq(lhs, rhs))
    }

    fn neq(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        let lhs = lhs.into_owned();
        let rhs = rhs.into_owned();
        if !lhs.check_same_sort(&rhs) {
            return Err(ClarirsError::TypeError(format!(
                "Sort mismatch in neq: {lhs:?} and {rhs:?}"
            )));
        }
        self.make_bool(AstOp::Neq(lhs, rhs))
    }

    fn neg(&'c self, ast: impl IntoOwned<AstRef<'c>>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::Neg(ast.into_owned()))
    }

    fn bv_and(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::And(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn bv_and_many(
        &'c self,
        args: impl IntoIterator<Item = AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        let args: Vec<AstRef<'c>> = args.into_iter().collect();
        self.make_bitvec(AstOp::And(args))
    }

    fn bv_or(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::Or(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn bv_or_many(
        &'c self,
        args: impl IntoIterator<Item = AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        let args: Vec<AstRef<'c>> = args.into_iter().collect();
        self.make_bitvec(AstOp::Or(args))
    }

    fn bv_xor(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::Xor(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn bv_xor_many(
        &'c self,
        args: impl IntoIterator<Item = AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        let args: Vec<AstRef<'c>> = args.into_iter().collect();
        self.make_bitvec(AstOp::Xor(args))
    }

    fn add(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::Add(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn add_many(
        &'c self,
        args: impl IntoIterator<Item = AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        let args: Vec<AstRef<'c>> = args.into_iter().collect();
        self.make_bitvec(AstOp::Add(args))
    }

    fn mul(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::Mul(vec![lhs.into_owned(), rhs.into_owned()]))
    }

    fn mul_many(
        &'c self,
        args: impl IntoIterator<Item = AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        let args: Vec<AstRef<'c>> = args.into_iter().collect();
        self.make_bitvec(AstOp::Mul(args))
    }

    fn sub(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::Sub(lhs.into_owned(), rhs.into_owned()))
    }

    fn udiv(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::UDiv(lhs.into_owned(), rhs.into_owned()))
    }

    fn sdiv(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::SDiv(lhs.into_owned(), rhs.into_owned()))
    }

    fn urem(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::URem(lhs.into_owned(), rhs.into_owned()))
    }

    fn srem(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::SRem(lhs.into_owned(), rhs.into_owned()))
    }

    fn shl(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::ShL(lhs.into_owned(), rhs.into_owned()))
    }

    fn ashr(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::AShR(lhs.into_owned(), rhs.into_owned()))
    }

    fn lshr(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::LShR(lhs.into_owned(), rhs.into_owned()))
    }

    fn rotate_left(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::RotateLeft(lhs.into_owned(), rhs.into_owned()))
    }

    fn rotate_right(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::RotateRight(lhs.into_owned(), rhs.into_owned()))
    }

    fn zero_ext(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        width: u32,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::ZeroExt(lhs.into_owned(), width))
    }

    fn sign_ext(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        width: u32,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::SignExt(lhs.into_owned(), width))
    }

    fn extract(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        high: u32,
        low: u32,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::Extract(lhs.into_owned(), high, low))
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
        self.make_bitvec(AstOp::Concat(args))
    }

    fn concat2(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.concat([lhs.into_owned(), rhs.into_owned()])
    }

    fn byte_reverse(&'c self, lhs: impl IntoOwned<AstRef<'c>>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::ByteReverse(lhs.into_owned()))
    }

    fn ult(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::ULT(lhs.into_owned(), rhs.into_owned()))
    }

    fn ule(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::ULE(lhs.into_owned(), rhs.into_owned()))
    }

    fn ugt(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::UGT(lhs.into_owned(), rhs.into_owned()))
    }

    fn uge(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::UGE(lhs.into_owned(), rhs.into_owned()))
    }

    fn slt(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::SLT(lhs.into_owned(), rhs.into_owned()))
    }

    fn sle(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::SLE(lhs.into_owned(), rhs.into_owned()))
    }

    fn sgt(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::SGT(lhs.into_owned(), rhs.into_owned()))
    }

    fn sge(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::SGE(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_to_fp<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        sort: FS,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_float(AstOp::FpToFp(lhs.into_owned(), sort.into(), rm.into()))
    }

    fn bv_to_fp<FS: Into<FSort>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        sort: FS,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_float(AstOp::BvToFp(lhs.into_owned(), sort.into()))
    }

    fn fp_fp(
        &'c self,
        sign: impl IntoOwned<AstRef<'c>>,
        exponent: impl IntoOwned<AstRef<'c>>,
        significand: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_float(AstOp::FpFP(
            sign.into_owned(),
            exponent.into_owned(),
            significand.into_owned(),
        ))
    }

    fn bv_to_fp_signed<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        sort: FS,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_float(AstOp::BvToFpSigned(
            lhs.into_owned(),
            sort.into(),
            rm.into(),
        ))
    }

    fn bv_to_fp_unsigned<RM: Into<FPRM>, FS: Into<FSort>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        sort: FS,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_float(AstOp::BvToFpUnsigned(
            lhs.into_owned(),
            sort.into(),
            rm.into(),
        ))
    }

    fn fp_to_ieeebv(&'c self, lhs: impl IntoOwned<AstRef<'c>>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::FpToIEEEBV(lhs.into_owned()))
    }

    fn fp_to_ubv<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        width: u32,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::FpToUBV(lhs.into_owned(), width, rm.into()))
    }

    fn fp_to_sbv<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        width: u32,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::FpToSBV(lhs.into_owned(), width, rm.into()))
    }

    fn fp_neg(&'c self, lhs: impl IntoOwned<AstRef<'c>>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_float(AstOp::FpNeg(lhs.into_owned()))
    }

    fn fp_abs(&'c self, lhs: impl IntoOwned<AstRef<'c>>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_float(AstOp::FpAbs(lhs.into_owned()))
    }

    fn fp_add<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_float(AstOp::FpAdd(lhs.into_owned(), rhs.into_owned(), rm.into()))
    }

    fn fp_sub<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_float(AstOp::FpSub(lhs.into_owned(), rhs.into_owned(), rm.into()))
    }

    fn fp_mul<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_float(AstOp::FpMul(lhs.into_owned(), rhs.into_owned(), rm.into()))
    }

    fn fp_div<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_float(AstOp::FpDiv(lhs.into_owned(), rhs.into_owned(), rm.into()))
    }

    fn fp_sqrt<RM: Into<FPRM>>(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rm: RM,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_float(AstOp::FpSqrt(lhs.into_owned(), rm.into()))
    }

    fn fp_eq(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::Eq(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_neq(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::Neq(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_lt(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::FpLt(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_leq(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::FpLeq(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_gt(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::FpGt(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_geq(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::FpGeq(lhs.into_owned(), rhs.into_owned()))
    }

    fn fp_is_nan(&'c self, lhs: impl IntoOwned<AstRef<'c>>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::FpIsNan(lhs.into_owned()))
    }

    fn fp_is_inf(&'c self, lhs: impl IntoOwned<AstRef<'c>>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::FpIsInf(lhs.into_owned()))
    }

    fn str_len(&'c self, lhs: impl IntoOwned<AstRef<'c>>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::StrLen(lhs.into_owned()))
    }

    fn str_concat(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_string(AstOp::StrConcat(lhs.into_owned(), rhs.into_owned()))
    }

    fn str_substr(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        start: impl IntoOwned<AstRef<'c>>,
        size: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_string(AstOp::StrSubstr(
            lhs.into_owned(),
            start.into_owned(),
            size.into_owned(),
        ))
    }

    fn str_contains(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::StrContains(lhs.into_owned(), rhs.into_owned()))
    }

    fn str_index_of(
        &'c self,
        base: impl IntoOwned<AstRef<'c>>,
        substr: impl IntoOwned<AstRef<'c>>,
        offset: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::StrIndexOf(
            base.into_owned(),
            substr.into_owned(),
            offset.into_owned(),
        ))
    }

    fn str_replace(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
        start: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_string(AstOp::StrReplace(
            lhs.into_owned(),
            rhs.into_owned(),
            start.into_owned(),
        ))
    }

    fn str_prefix_of(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::StrPrefixOf(lhs.into_owned(), rhs.into_owned()))
    }

    fn str_suffix_of(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::StrSuffixOf(lhs.into_owned(), rhs.into_owned()))
    }

    fn str_to_bv(&'c self, lhs: impl IntoOwned<AstRef<'c>>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::StrToBV(lhs.into_owned()))
    }

    fn bv_to_str(&'c self, lhs: impl IntoOwned<AstRef<'c>>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_string(AstOp::BVToStr(lhs.into_owned()))
    }

    fn str_is_digit(&'c self, lhs: impl IntoOwned<AstRef<'c>>) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::StrIsDigit(lhs.into_owned()))
    }

    fn str_eq(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::Eq(lhs.into_owned(), rhs.into_owned()))
    }

    fn str_neq(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bool(AstOp::Neq(lhs.into_owned(), rhs.into_owned()))
    }

    /// If-then-else. `then` and `else_` must have the same sort.
    fn ite(
        &'c self,
        cond: impl IntoOwned<AstRef<'c>>,
        then: impl IntoOwned<AstRef<'c>>,
        else_: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        let cond = cond.into_owned();
        let then = then.into_owned();
        let else_ = else_.into_owned();
        if !cond.ty().is_bool() {
            return Err(ClarirsError::TypeError(format!(
                "ite() condition must be boolean, got {:?}",
                cond.ty()
            )));
        }
        if !then.check_same_sort(&else_) {
            return Err(ClarirsError::TypeError(format!(
                "Sort mismatch in if-then-else: {then:?} and {else_:?}"
            )));
        }
        self.make(AstOp::ITE(cond, then, else_))
    }

    fn annotate(
        &'c self,
        ast: impl IntoOwned<AstRef<'c>>,
        annotations: impl IntoIterator<Item = Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        ast.into_owned().annotate(annotations)
    }

    fn annotate_dyn(
        &'c self,
        ast: impl IntoOwned<AstRef<'c>>,
        annotations: Vec<Annotation>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        ast.into_owned().annotate(annotations)
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
        self.make_bitvec_annotated(
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
        self.make_bitvec_annotated(
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
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::Union(lhs.into_owned(), rhs.into_owned()))
    }

    fn intersection(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::Intersection(lhs.into_owned(), rhs.into_owned()))
    }

    fn widen(
        &'c self,
        lhs: impl IntoOwned<AstRef<'c>>,
        rhs: impl IntoOwned<AstRef<'c>>,
    ) -> Result<AstRef<'c>, ClarirsError> {
        self.make_bitvec(AstOp::Widen(lhs.into_owned(), rhs.into_owned()))
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
