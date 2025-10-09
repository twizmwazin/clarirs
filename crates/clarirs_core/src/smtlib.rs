use crate::{algorithms::walk_post_order, prelude::*};

/// TODO: I generated these implementations to facilitate debug printing, but
/// have not verified them for correctness.
fn to_smtlib_bool(ast: &BoolAst, children: &[String]) -> String {
    match ast.op() {
        BooleanOp::BoolS(s) => s.clone(),
        BooleanOp::BoolV(b) => b.to_string(),
        BooleanOp::Not(..) => format!("(not {})", children[0]),
        BooleanOp::And(..) => format!("(and {} {})", children[0], children[1]),
        BooleanOp::Or(..) => format!("(or {} {})", children[0], children[1]),
        BooleanOp::Xor(..) => format!("(xor {} {})", children[0], children[1]),
        BooleanOp::BoolEq(..) => format!("(= {} {})", children[0], children[1]),
        BooleanOp::BoolNeq(..) => format!("(not (= {} {}))", children[0], children[1]),
        BooleanOp::Eq(..) => format!("(= {} {})", children[0], children[1]),
        BooleanOp::Neq(..) => format!("(not (= {} {}))", children[0], children[1]),
        BooleanOp::ULT(..) => format!("(bvult {} {})", children[0], children[1]),
        BooleanOp::ULE(..) => format!("(bvule {} {})", children[0], children[1]),
        BooleanOp::UGT(..) => format!("(bvugt {} {})", children[0], children[1]),
        BooleanOp::UGE(..) => format!("(bvuge {} {})", children[0], children[1]),
        BooleanOp::SLT(..) => format!("(bvslt {} {})", children[0], children[1]),
        BooleanOp::SLE(..) => format!("(bvsle {} {})", children[0], children[1]),
        BooleanOp::SGT(..) => format!("(bvsgt {} {})", children[0], children[1]),
        BooleanOp::SGE(..) => format!("(bvsge {} {})", children[0], children[1]),
        BooleanOp::FpEq(..) => format!("(fp.eq {} {})", children[0], children[1]),
        BooleanOp::FpNeq(..) => format!("(not (fp.eq {} {}))", children[0], children[1]),
        BooleanOp::FpLt(..) => format!("(fp.lt {} {})", children[0], children[1]),
        BooleanOp::FpLeq(..) => format!("(fp.leq {} {})", children[0], children[1]),
        BooleanOp::FpGt(..) => format!("(fp.gt {} {})", children[0], children[1]),
        BooleanOp::FpGeq(..) => format!("(fp.geq {} {})", children[0], children[1]),
        BooleanOp::FpIsNan(..) => format!("(fp.isNaN {})", children[0]),
        BooleanOp::FpIsInf(..) => format!("(fp.isInfinite {})", children[0]),
        BooleanOp::StrContains(..) => format!("(str.contains {} {})", children[0], children[1]),
        BooleanOp::StrPrefixOf(..) => format!("(str.prefixof {} {})", children[0], children[1]),
        BooleanOp::StrSuffixOf(..) => format!("(str.suffixof {} {})", children[0], children[1]),
        BooleanOp::StrIsDigit(..) => format!("(str.is_digit {})", children[0]),
        BooleanOp::StrEq(..) => format!("(= {} {})", children[0], children[1]),
        BooleanOp::StrNeq(..) => format!("(not (= {} {}))", children[0], children[1]),
        BooleanOp::If(..) => format!("(ite {} {} {})", children[0], children[1], children[2]),
    }
}

fn to_smtlib_bv(ast: &BitVecAst, children: &[String]) -> String {
    match ast.op() {
        BitVecOp::BVS(s, _) => s.clone(),
        BitVecOp::BVV(bit_vec) => format!("(_ bv{} {})", bit_vec.to_biguint(), bit_vec.len()),
        BitVecOp::Not(..) => format!("(bvnot {})", children[0]),
        BitVecOp::And(..) => format!("(bvand {} {})", children[0], children[1]),
        BitVecOp::Or(..) => format!("(bvor {} {})", children[0], children[1]),
        BitVecOp::Xor(..) => format!("(bvxor {} {})", children[0], children[1]),
        BitVecOp::Neg(..) => format!("(bvneg {})", children[0]),
        BitVecOp::Add(..) => format!("(bvadd {} {})", children[0], children[1]),
        BitVecOp::Sub(..) => format!("(bvsub {} {})", children[0], children[1]),
        BitVecOp::Mul(..) => format!("(bvmul {} {})", children[0], children[1]),
        BitVecOp::UDiv(..) => format!("(bvudiv {} {})", children[0], children[1]),
        BitVecOp::SDiv(..) => format!("(bvsdiv {} {})", children[0], children[1]),
        BitVecOp::URem(..) => format!("(bvurem {} {})", children[0], children[1]),
        BitVecOp::SRem(..) => format!("(bvsrem {} {})", children[0], children[1]),
        BitVecOp::ShL(..) => format!("(bvshl {} {})", children[0], children[1]),
        BitVecOp::LShR(..) => format!("(bvlshr {} {})", children[0], children[1]),
        BitVecOp::AShR(..) => format!("(bvashr {} {})", children[0], children[1]),
        BitVecOp::RotateLeft(..) => format!("(rotate_left {} {})", children[0], children[1]),
        BitVecOp::RotateRight(..) => format!("(rotate_right {} {})", children[0], children[1]),
        BitVecOp::ZeroExt(_, size) => format!("((_ zero_extend {}) {})", size, children[0]),
        BitVecOp::SignExt(_, size) => format!("((_ sign_extend {}) {})", size, children[0]),
        BitVecOp::Extract(_, high, low) => {
            format!("((_ extract {} {}) {})", high, low, children[0])
        }
        BitVecOp::Concat(..) => format!("(concat {} {})", children[0], children[1]),
        BitVecOp::Reverse(..) => format!("(bvreverse {})", children[0]),
        BitVecOp::FpToIEEEBV(..) => format!("(fp.to_ieee_bv {})", children[0]),
        BitVecOp::FpToUBV(_, size, fprm) => format!(
            "((_ fp.to_ubv {}) {} {})",
            size,
            format!("{fprm:?}").to_lowercase(),
            children[0]
        ),
        BitVecOp::FpToSBV(_, size, fprm) => format!(
            "((_ fp.to_sbv {}) {} {})",
            size,
            format!("{fprm:?}").to_lowercase(),
            children[0]
        ),
        BitVecOp::StrLen(..) => format!("(str.len {})", children[0]),
        BitVecOp::StrIndexOf(..) => {
            format!(
                "(str.indexof {} {} {})",
                children[0], children[1], children[2]
            )
        }
        BitVecOp::StrToBV(..) => format!("(str.to_bv {})", children[0]),
        BitVecOp::If(..) => format!("(ite {} {} {})", children[0], children[1], children[2]),
        BitVecOp::SI(size, stride, lb, ub) => format!("(vsasi {size} {stride} {lb} {ub})"),
        BitVecOp::Union(..) => format!("(vsaunion {} {})", children[0], children[1]),
        BitVecOp::Intersection(..) => format!("(vsaintersection {} {})", children[0], children[1]),
    }
}

fn to_smtlib_float(ast: &FloatAst, children: &[String]) -> String {
    match ast.op() {
        FloatOp::FPS(s, _) => s.clone(),
        FloatOp::FPV(float) => {
            let sign = if float.sign() { "1" } else { "0" };
            let exp = float.exponent().to_biguint().to_string();
            let sig = float.mantissa().to_biguint().to_string();
            format!("(fp #{sign} #{exp} #{sig})")
        }
        FloatOp::FpNeg(..) => format!("(fp.neg {})", children[0]),
        FloatOp::FpAbs(..) => format!("(fp.abs {})", children[0]),
        FloatOp::FpAdd(_, _, fprm) => format!(
            "(fp.add {} {} {})",
            format!("{fprm:?}").to_lowercase(),
            children[0],
            children[1]
        ),
        FloatOp::FpSub(_, _, fprm) => format!(
            "(fp.sub {} {} {})",
            format!("{fprm:?}").to_lowercase(),
            children[0],
            children[1]
        ),
        FloatOp::FpMul(_, _, fprm) => format!(
            "(fp.mul {} {} {})",
            format!("{fprm:?}").to_lowercase(),
            children[0],
            children[1]
        ),
        FloatOp::FpDiv(_, _, fprm) => format!(
            "(fp.div {} {} {})",
            format!("{fprm:?}").to_lowercase(),
            children[0],
            children[1]
        ),
        FloatOp::FpSqrt(_, fprm) => format!(
            "(fp.sqrt {} {})",
            format!("{fprm:?}").to_lowercase(),
            children[0]
        ),
        FloatOp::FpToFp(_, fsort, fprm) => format!(
            "((_ to_fp {} {}) {} {})",
            fsort.exponent,
            fsort.mantissa,
            format!("{fprm:?}").to_lowercase(),
            children[0]
        ),
        FloatOp::BvToFp(_, fsort) => format!(
            "((_ to_fp {} {}) {})",
            fsort.exponent, fsort.mantissa, children[0]
        ),
        FloatOp::BvToFpSigned(_, fsort, fprm) => format!(
            "((_ to_fp {} {}) {} {})",
            fsort.exponent,
            fsort.mantissa,
            format!("{fprm:?}").to_lowercase(),
            children[0]
        ),
        FloatOp::BvToFpUnsigned(_, fsort, fprm) => format!(
            "((_ to_fp_unsigned {} {}) {} {})",
            fsort.exponent,
            fsort.mantissa,
            format!("{fprm:?}").to_lowercase(),
            children[0]
        ),
        FloatOp::If(..) => {
            format!("(ite {} {} {})", children[0], children[1], children[2])
        }
    }
}

fn to_smtlib_string(ast: &StringAst, children: &[String]) -> String {
    match ast.op() {
        StringOp::StringS(s) => s.clone(),
        StringOp::StringV(s) => format!("\"{}\"", s.replace("\"", "\\\"")),
        StringOp::StrConcat(..) => format!("(str.++ {} {})", children[0], children[1]),
        StringOp::StrSubstr(..) => format!(
            "(str.substr {} {} {})",
            children[0], children[1], children[2]
        ),
        StringOp::StrReplace(..) => format!(
            "(str.replace {} {} {})",
            children[0], children[1], children[2]
        ),
        StringOp::BVToStr(..) => format!("(str.from_bv {})", children[0]),
        StringOp::If(..) => format!("(ite {} {} {})", children[0], children[1], children[2]),
    }
}

/// Trait for converting an AST to a SMT-LIB string.
pub trait ToSmtLib {
    fn to_smtlib(&self) -> String;
}

impl ToSmtLib for DynAst<'_> {
    fn to_smtlib(&self) -> String {
        walk_post_order(
            self.clone(),
            |node, children| match node {
                DynAst::Boolean(ast) => Ok(to_smtlib_bool(&ast, children)),
                DynAst::BitVec(ast) => Ok(to_smtlib_bv(&ast, children)),
                DynAst::Float(ast) => Ok(to_smtlib_float(&ast, children)),
                DynAst::String(ast) => Ok(to_smtlib_string(&ast, children)),
            },
            &(),
        )
        .expect("infallible")
    }
}

impl ToSmtLib for BoolAst<'_> {
    fn to_smtlib(&self) -> String {
        DynAst::from(self).to_smtlib()
    }
}

impl ToSmtLib for BitVecAst<'_> {
    fn to_smtlib(&self) -> String {
        DynAst::from(self).to_smtlib()
    }
}

impl ToSmtLib for FloatAst<'_> {
    fn to_smtlib(&self) -> String {
        DynAst::from(self).to_smtlib()
    }
}

impl ToSmtLib for StringAst<'_> {
    fn to_smtlib(&self) -> String {
        DynAst::from(self).to_smtlib()
    }
}
