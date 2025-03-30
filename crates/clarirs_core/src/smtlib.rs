use crate::prelude::*;

/// Trait for converting an AST to a SMT-LIB string.
pub trait ToSmtLib {
    fn to_smtlib(&self) -> String;
}

/// TODO: I generated these implementations to facilitate debug printing, but
/// have not verified them for correctness.
impl ToSmtLib for BoolAst<'_> {
    fn to_smtlib(&self) -> String {
        match self.op() {
            BooleanOp::BoolS(s) => s.clone(),
            BooleanOp::BoolV(b) => {
                if *b {
                    "true".to_string()
                } else {
                    "false".to_string()
                }
            }
            BooleanOp::Not(ast) => format!("(not {})", ast.to_smtlib()),
            BooleanOp::And(lhs, rhs) => format!("(and {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::Or(lhs, rhs) => format!("(or {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::Xor(lhs, rhs) => format!("(xor {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::BoolEq(lhs, rhs) => format!("(= {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::BoolNeq(lhs, rhs) => {
                format!("(not (= {} {}))", lhs.to_smtlib(), rhs.to_smtlib())
            }
            BooleanOp::Eq(lhs, rhs) => format!("(= {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::Neq(lhs, rhs) => {
                format!("(not (= {} {}))", lhs.to_smtlib(), rhs.to_smtlib())
            }
            BooleanOp::ULT(lhs, rhs) => format!("(bvult {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::ULE(lhs, rhs) => format!("(bvule {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::UGT(lhs, rhs) => format!("(bvugt {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::UGE(lhs, rhs) => format!("(bvuge {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::SLT(lhs, rhs) => format!("(bvslt {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::SLE(lhs, rhs) => format!("(bvsle {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::SGT(lhs, rhs) => format!("(bvsgt {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::SGE(lhs, rhs) => format!("(bvsge {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::FpEq(lhs, rhs) => format!("(fp.eq {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::FpNeq(lhs, rhs) => {
                format!("(not (fp.eq {} {}))", lhs.to_smtlib(), rhs.to_smtlib())
            }
            BooleanOp::FpLt(lhs, rhs) => format!("(fp.lt {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::FpLeq(lhs, rhs) => {
                format!("(fp.leq {} {})", lhs.to_smtlib(), rhs.to_smtlib())
            }
            BooleanOp::FpGt(lhs, rhs) => format!("(fp.gt {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::FpGeq(lhs, rhs) => {
                format!("(fp.geq {} {})", lhs.to_smtlib(), rhs.to_smtlib())
            }
            BooleanOp::FpIsNan(ast) => format!("(fp.isNaN {})", ast.to_smtlib()),
            BooleanOp::FpIsInf(ast) => format!("(fp.isInfinite {})", ast.to_smtlib()),
            BooleanOp::StrContains(lhs, rhs) => {
                format!("(str.contains {} {})", lhs.to_smtlib(), rhs.to_smtlib())
            }
            BooleanOp::StrPrefixOf(lhs, rhs) => {
                format!("(str.prefixof {} {})", lhs.to_smtlib(), rhs.to_smtlib())
            }
            BooleanOp::StrSuffixOf(lhs, rhs) => {
                format!("(str.suffixof {} {})", lhs.to_smtlib(), rhs.to_smtlib())
            }
            BooleanOp::StrIsDigit(ast) => format!("(str.is_digit {})", ast.to_smtlib()),
            BooleanOp::StrEq(lhs, rhs) => format!("(= {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BooleanOp::StrNeq(lhs, rhs) => {
                format!("(not (= {} {}))", lhs.to_smtlib(), rhs.to_smtlib())
            }
            BooleanOp::If(cond, then_, else_) => format!(
                "(ite {} {} {})",
                cond.to_smtlib(),
                then_.to_smtlib(),
                else_.to_smtlib()
            ),
            BooleanOp::Annotated(ast, _) => ast.to_smtlib(),
        }
    }
}

impl ToSmtLib for BitVecAst<'_> {
    fn to_smtlib(&self) -> String {
        match self.op() {
            BitVecOp::BVS(s, _) => s.clone(),
            BitVecOp::BVV(bit_vec) => format!("(_ bv{} {})", bit_vec.to_biguint(), bit_vec.len()),
            BitVecOp::Not(ast) => format!("(bvnot {})", ast.to_smtlib()),
            BitVecOp::And(lhs, rhs) => format!("(bvand {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BitVecOp::Or(lhs, rhs) => format!("(bvor {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BitVecOp::Xor(lhs, rhs) => format!("(bvxor {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BitVecOp::Neg(ast) => format!("(bvneg {})", ast.to_smtlib()),
            BitVecOp::Add(lhs, rhs) => format!("(bvadd {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BitVecOp::Sub(lhs, rhs) => format!("(bvsub {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BitVecOp::Mul(lhs, rhs) => format!("(bvmul {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BitVecOp::UDiv(lhs, rhs) => format!("(bvudiv {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BitVecOp::SDiv(lhs, rhs) => format!("(bvsdiv {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BitVecOp::URem(lhs, rhs) => format!("(bvurem {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BitVecOp::SRem(lhs, rhs) => format!("(bvsrem {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BitVecOp::ShL(lhs, rhs) => format!("(bvshl {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BitVecOp::LShR(lhs, rhs) => format!("(bvlshr {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BitVecOp::AShR(lhs, rhs) => format!("(bvashr {} {})", lhs.to_smtlib(), rhs.to_smtlib()),
            BitVecOp::RotateLeft(lhs, rhs) => {
                format!("(rotate_left {} {})", lhs.to_smtlib(), rhs.to_smtlib())
            }
            BitVecOp::RotateRight(lhs, rhs) => {
                format!("(rotate_right {} {})", lhs.to_smtlib(), rhs.to_smtlib())
            }
            BitVecOp::ZeroExt(ast, size) => {
                format!("((_ zero_extend {}) {})", size, ast.to_smtlib())
            }
            BitVecOp::SignExt(ast, size) => {
                format!("((_ sign_extend {}) {})", size, ast.to_smtlib())
            }
            BitVecOp::Extract(ast, high, low) => {
                format!("((_ extract {} {}) {})", high, low, ast.to_smtlib())
            }
            BitVecOp::Concat(lhs, rhs) => {
                format!("(concat {} {})", lhs.to_smtlib(), rhs.to_smtlib())
            }
            BitVecOp::Reverse(ast) => format!("(bvreverse {})", ast.to_smtlib()),
            BitVecOp::FpToIEEEBV(ast) => format!("(fp.to_ieee_bv {})", ast.to_smtlib()),
            BitVecOp::FpToUBV(ast, size, fprm) => format!(
                "((_ fp.to_ubv {}) {} {})",
                size,
                format!("{:?}", fprm).to_lowercase(),
                ast.to_smtlib()
            ),
            BitVecOp::FpToSBV(ast, size, fprm) => format!(
                "((_ fp.to_sbv {}) {} {})",
                size,
                format!("{:?}", fprm).to_lowercase(),
                ast.to_smtlib()
            ),
            BitVecOp::StrLen(ast) => format!("(str.len {})", ast.to_smtlib()),
            BitVecOp::StrIndexOf(lhs, rhs, ast2) => format!(
                "(str.indexof {} {} {})",
                lhs.to_smtlib(),
                rhs.to_smtlib(),
                ast2.to_smtlib()
            ),
            BitVecOp::StrToBV(ast) => format!("(str.to_bv {})", ast.to_smtlib()),
            BitVecOp::If(cond, then_, else_) => format!(
                "(ite {} {} {})",
                cond.to_smtlib(),
                then_.to_smtlib(),
                else_.to_smtlib()
            ),
            BitVecOp::Annotated(ast, _) => ast.to_smtlib(),
            BitVecOp::SI(size, stride, lb, ub) => {
                format!("(vsasi {} {} {} {})", size, stride, lb, ub)
            }
            BitVecOp::Union(lhs, rhs) => {
                format!("(vsaunion {} {})", lhs.to_smtlib(), rhs.to_smtlib())
            }
            BitVecOp::Intersection(lhs, rhs) => {
                format!("(vsaintersection {} {})", lhs.to_smtlib(), rhs.to_smtlib())
            }
        }
    }
}

impl ToSmtLib for FloatAst<'_> {
    fn to_smtlib(&self) -> String {
        match self.op() {
            FloatOp::FPS(s, _) => s.clone(),
            FloatOp::FPV(float) => {
                let sign = if float.sign() { "1" } else { "0" };
                let exp = float.exponent().to_biguint().to_string();
                let sig = float.mantissa().to_biguint().to_string();
                format!("(fp #{} #{} #{})", sign, exp, sig)
            }
            FloatOp::FpNeg(ast) => format!("(fp.neg {})", ast.to_smtlib()),
            FloatOp::FpAbs(ast) => format!("(fp.abs {})", ast.to_smtlib()),
            FloatOp::FpAdd(lhs, rhs, fprm) => format!(
                "(fp.add {} {} {})",
                format!("{:?}", fprm).to_lowercase(),
                lhs.to_smtlib(),
                rhs.to_smtlib()
            ),
            FloatOp::FpSub(lhs, rhs, fprm) => format!(
                "(fp.sub {} {} {})",
                format!("{:?}", fprm).to_lowercase(),
                lhs.to_smtlib(),
                rhs.to_smtlib()
            ),
            FloatOp::FpMul(lhs, rhs, fprm) => format!(
                "(fp.mul {} {} {})",
                format!("{:?}", fprm).to_lowercase(),
                lhs.to_smtlib(),
                rhs.to_smtlib()
            ),
            FloatOp::FpDiv(lhs, rhs, fprm) => format!(
                "(fp.div {} {} {})",
                format!("{:?}", fprm).to_lowercase(),
                lhs.to_smtlib(),
                rhs.to_smtlib()
            ),
            FloatOp::FpSqrt(ast, fprm) => format!(
                "(fp.sqrt {} {})",
                format!("{:?}", fprm).to_lowercase(),
                ast.to_smtlib()
            ),
            FloatOp::FpToFp(ast, fsort, fprm) => format!(
                "((_ to_fp {} {}) {} {})",
                fsort.exponent,
                fsort.mantissa,
                format!("{:?}", fprm).to_lowercase(),
                ast.to_smtlib()
            ),
            FloatOp::BvToFp(ast, fsort) => format!(
                "((_ to_fp {} {}) {})",
                fsort.exponent,
                fsort.mantissa,
                ast.to_smtlib()
            ),
            FloatOp::BvToFpSigned(ast, fsort, fprm) => format!(
                "((_ to_fp {} {}) {} {})",
                fsort.exponent,
                fsort.mantissa,
                format!("{:?}", fprm).to_lowercase(),
                ast.to_smtlib()
            ),
            FloatOp::BvToFpUnsigned(ast, fsort, fprm) => format!(
                "((_ to_fp_unsigned {} {}) {} {})",
                fsort.exponent,
                fsort.mantissa,
                format!("{:?}", fprm).to_lowercase(),
                ast.to_smtlib()
            ),
            FloatOp::If(cond, then_, else_) => format!(
                "(ite {} {} {})",
                cond.to_smtlib(),
                then_.to_smtlib(),
                else_.to_smtlib()
            ),
            FloatOp::Annotated(ast, _) => ast.to_smtlib(),
        }
    }
}

impl ToSmtLib for StringAst<'_> {
    fn to_smtlib(&self) -> String {
        match self.op() {
            StringOp::StringS(s) => s.clone(),
            StringOp::StringV(s) => format!("\"{}\"", s.replace("\"", "\\\"")),
            StringOp::StrConcat(lhs, rhs) => {
                format!("(str.++ {} {})", lhs.to_smtlib(), rhs.to_smtlib())
            }
            StringOp::StrSubstr(lhs, rhs, ast2) => format!(
                "(str.substr {} {} {})",
                lhs.to_smtlib(),
                rhs.to_smtlib(),
                ast2.to_smtlib()
            ),
            StringOp::StrReplace(lhs, rhs, ast2) => format!(
                "(str.replace {} {} {})",
                lhs.to_smtlib(),
                rhs.to_smtlib(),
                ast2.to_smtlib()
            ),
            StringOp::BVToStr(ast) => format!("(str.from_bv {})", ast.to_smtlib()),
            StringOp::If(cond, then_, else_) => format!(
                "(ite {} {} {})",
                cond.to_smtlib(),
                then_.to_smtlib(),
                else_.to_smtlib()
            ),
            StringOp::Annotated(ast, _) => ast.to_smtlib(),
        }
    }
}

impl ToSmtLib for DynAst<'_> {
    fn to_smtlib(&self) -> String {
        match self {
            DynAst::Boolean(ast) => ast.to_smtlib(),
            DynAst::BitVec(ast) => ast.to_smtlib(),
            DynAst::Float(ast) => ast.to_smtlib(),
            DynAst::String(ast) => ast.to_smtlib(),
        }
    }
}
