use std::fmt;

use crate::{algorithms::walk_post_order, prelude::*};

/// Converts an FPRM rounding mode to its SMT-LIB 2.6 identifier.
fn fprm_to_smtlib(fprm: &FPRM) -> &'static str {
    match fprm {
        FPRM::NearestTiesToEven => "RNE",
        FPRM::NearestTiesToAway => "RNA",
        FPRM::TowardPositive => "RTP",
        FPRM::TowardNegative => "RTN",
        FPRM::TowardZero => "RTZ",
    }
}

fn to_smtlib_bool(ast: &BoolAst, children: &[String]) -> String {
    match ast.op() {
        BooleanOp::BoolS(s) => s.to_string(),
        BooleanOp::BoolV(b) => b.to_string(),
        BooleanOp::Not(..) => format!("(not {})", children[0]),
        BooleanOp::And(..) => format!("(and {})", children.join(" ")),
        BooleanOp::Or(..) => format!("(or {})", children.join(" ")),
        BooleanOp::Xor(..) => format!("(xor {} {})", children[0], children[1]),
        BooleanOp::BoolEq(..) => format!("(= {} {})", children[0], children[1]),
        BooleanOp::BoolNeq(..) => {
            format!("(distinct {} {})", children[0], children[1])
        }
        BooleanOp::Eq(..) => format!("(= {} {})", children[0], children[1]),
        BooleanOp::Neq(..) => {
            format!("(distinct {} {})", children[0], children[1])
        }
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
        BooleanOp::ITE(..) => format!("(ite {} {} {})", children[0], children[1], children[2]),
    }
}

fn to_smtlib_bv(ast: &BitVecAst, children: &[String]) -> String {
    match ast.op() {
        BitVecOp::BVS(s, _) => s.to_string(),
        BitVecOp::BVV(bit_vec) => format!("(_ bv{} {})", bit_vec.to_biguint(), bit_vec.len()),
        BitVecOp::Not(..) => format!("(bvnot {})", children[0]),
        BitVecOp::And(..) => children.iter().skip(1).fold(children[0].clone(), |acc, c| format!("(bvand {} {})", acc, c)),
        BitVecOp::Or(..) => children.iter().skip(1).fold(children[0].clone(), |acc, c| format!("(bvor {} {})", acc, c)),
        BitVecOp::Xor(..) => children.iter().skip(1).fold(children[0].clone(), |acc, c| format!("(bvxor {} {})", acc, c)),
        BitVecOp::Neg(..) => format!("(bvneg {})", children[0]),
        BitVecOp::Add(..) => children.iter().skip(1).fold(children[0].clone(), |acc, c| format!("(bvadd {} {})", acc, c)),
        BitVecOp::Sub(..) => format!("(bvsub {} {})", children[0], children[1]),
        BitVecOp::Mul(..) => children.iter().skip(1).fold(children[0].clone(), |acc, c| format!("(bvmul {} {})", acc, c)),
        BitVecOp::UDiv(..) => format!("(bvudiv {} {})", children[0], children[1]),
        BitVecOp::SDiv(..) => format!("(bvsdiv {} {})", children[0], children[1]),
        BitVecOp::URem(..) => format!("(bvurem {} {})", children[0], children[1]),
        BitVecOp::SRem(..) => format!("(bvsrem {} {})", children[0], children[1]),
        BitVecOp::ShL(..) => format!("(bvshl {} {})", children[0], children[1]),
        BitVecOp::LShR(..) => format!("(bvlshr {} {})", children[0], children[1]),
        BitVecOp::AShR(..) => format!("(bvashr {} {})", children[0], children[1]),
        BitVecOp::RotateLeft(..) => {
            format!("(ext_rotate_left {} {})", children[0], children[1])
        }
        BitVecOp::RotateRight(..) => {
            format!("(ext_rotate_right {} {})", children[0], children[1])
        }
        BitVecOp::ZeroExt(_, size) => format!("((_ zero_extend {}) {})", size, children[0]),
        BitVecOp::SignExt(_, size) => format!("((_ sign_extend {}) {})", size, children[0]),
        BitVecOp::Extract(_, high, low) => {
            format!("((_ extract {} {}) {})", high, low, children[0])
        }
        BitVecOp::Concat(..) => format!("(concat {})", children.join(" ")),
        BitVecOp::ByteReverse(..) => format!("(bvreverse {})", children[0]),
        BitVecOp::FpToIEEEBV(..) => format!("(fp.to_ieee_bv {})", children[0]),
        BitVecOp::FpToUBV(_, size, fprm) => format!(
            "((_ fp.to_ubv {}) {} {})",
            size,
            fprm_to_smtlib(fprm),
            children[0]
        ),
        BitVecOp::FpToSBV(_, size, fprm) => format!(
            "((_ fp.to_sbv {}) {} {})",
            size,
            fprm_to_smtlib(fprm),
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
        BitVecOp::ITE(..) => format!("(ite {} {} {})", children[0], children[1], children[2]),
        BitVecOp::Union(..) => format!("(vsaunion {} {})", children[0], children[1]),
        BitVecOp::Intersection(..) => {
            format!("(vsaintersection {} {})", children[0], children[1])
        }
        BitVecOp::Widen(..) => format!("(vsawiden {} {})", children[0], children[1]),
    }
}

fn to_smtlib_float(ast: &FloatAst, children: &[String]) -> String {
    match ast.op() {
        FloatOp::FPS(s, _) => s.to_string(),
        FloatOp::FPV(float) => {
            let sign = if float.sign() { "#b1" } else { "#b0" };
            let exp = float.exponent();
            let sig = float.mantissa();
            let exp_str = format!("{:0>width$b}", exp.to_biguint(), width = exp.len() as usize);
            let sig_str = format!("{:0>width$b}", sig.to_biguint(), width = sig.len() as usize);
            format!("(fp {sign} #b{exp_str} #b{sig_str})")
        }
        FloatOp::FpFP(..) => format!("(fp {} {} {})", children[0], children[1], children[2]),
        FloatOp::FpNeg(..) => format!("(fp.neg {})", children[0]),
        FloatOp::FpAbs(..) => format!("(fp.abs {})", children[0]),
        FloatOp::FpAdd(_, _, fprm) => format!(
            "(fp.add {} {} {})",
            fprm_to_smtlib(fprm),
            children[0],
            children[1]
        ),
        FloatOp::FpSub(_, _, fprm) => format!(
            "(fp.sub {} {} {})",
            fprm_to_smtlib(fprm),
            children[0],
            children[1]
        ),
        FloatOp::FpMul(_, _, fprm) => format!(
            "(fp.mul {} {} {})",
            fprm_to_smtlib(fprm),
            children[0],
            children[1]
        ),
        FloatOp::FpDiv(_, _, fprm) => format!(
            "(fp.div {} {} {})",
            fprm_to_smtlib(fprm),
            children[0],
            children[1]
        ),
        FloatOp::FpSqrt(_, fprm) => format!("(fp.sqrt {} {})", fprm_to_smtlib(fprm), children[0]),
        FloatOp::FpToFp(_, fsort, fprm) => format!(
            "((_ to_fp {} {}) {} {})",
            fsort.exponent,
            fsort.mantissa,
            fprm_to_smtlib(fprm),
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
            fprm_to_smtlib(fprm),
            children[0]
        ),
        FloatOp::BvToFpUnsigned(_, fsort, fprm) => format!(
            "((_ to_fp_unsigned {} {}) {} {})",
            fsort.exponent,
            fsort.mantissa,
            fprm_to_smtlib(fprm),
            children[0]
        ),
        FloatOp::ITE(..) => {
            format!("(ite {} {} {})", children[0], children[1], children[2])
        }
    }
}

fn to_smtlib_string(ast: &StringAst, children: &[String]) -> String {
    match ast.op() {
        StringOp::StringS(s) => s.to_string(),
        StringOp::StringV(s) => format!("\"{}\"", s.replace('"', "\\\"")),
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
        StringOp::ITE(..) => format!("(ite {} {} {})", children[0], children[1], children[2]),
    }
}

/// Trait for converting an AST to an SMT-LIB 2.6 string representation.
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

/// Blanket `Display` implementation for any type implementing `ToSmtLib`.
impl<T: ToSmtLib> fmt::Display for SmtLibDisplay<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.to_smtlib())
    }
}

/// Wrapper to display any `ToSmtLib` type via `fmt::Display`.
///
/// # Example
/// ```ignore
/// use clarirs_core::smtlib::{SmtLibDisplay, ToSmtLib};
/// let ast = ctx.bvs("x", 64).unwrap();
/// println!("{}", SmtLibDisplay(&ast));
/// ```
pub struct SmtLibDisplay<'a, T: ToSmtLib>(pub &'a T);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bool_value() {
        let ctx = Context::new();
        let t = ctx.true_().unwrap();
        let f = ctx.false_().unwrap();
        assert_eq!(t.to_smtlib(), "true");
        assert_eq!(f.to_smtlib(), "false");
    }

    #[test]
    fn test_bool_ops() {
        let ctx = Context::new();
        let a = ctx.bools("a").unwrap();
        let b = ctx.bools("b").unwrap();

        let not_a = ctx.not(&a).unwrap();
        assert_eq!(not_a.to_smtlib(), "(not a)");

        let and = ctx.and([a.clone(), b.clone()]).unwrap();
        assert_eq!(and.to_smtlib(), "(and a b)");

        let or = ctx.or([a.clone(), b.clone()]).unwrap();
        assert_eq!(or.to_smtlib(), "(or a b)");
    }

    #[test]
    fn test_bv_symbol_and_value() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();
        assert_eq!(x.to_smtlib(), "x");

        let v = ctx.bvv_prim(42u64).unwrap();
        assert_eq!(v.to_smtlib(), "(_ bv42 64)");
    }

    #[test]
    fn test_bv_arithmetic() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 64).unwrap();
        let y = ctx.bvs("y", 64).unwrap();

        let add = ctx.add(&x, &y).unwrap();
        assert_eq!(add.to_smtlib(), "(bvadd x y)");

        let sub = ctx.sub(&x, &y).unwrap();
        assert_eq!(sub.to_smtlib(), "(bvsub x y)");
    }

    #[test]
    fn test_bv_comparisons() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 64).unwrap();
        let y = ctx.bvs("y", 64).unwrap();

        let ult = ctx.ult(&x, &y).unwrap();
        assert_eq!(ult.to_smtlib(), "(bvult x y)");

        let sge = ctx.sge(&x, &y).unwrap();
        assert_eq!(sge.to_smtlib(), "(bvsge x y)");
    }

    #[test]
    fn test_neq_uses_distinct() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 64).unwrap();
        let y = ctx.bvs("y", 64).unwrap();

        let neq = ctx.neq(&x, &y).unwrap();
        assert_eq!(neq.to_smtlib(), "(distinct x y)");
    }

    #[test]
    fn test_extract_and_extend() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();

        let ext = ctx.extract(&x, 15, 8).unwrap();
        assert_eq!(ext.to_smtlib(), "((_ extract 15 8) x)");

        let zext = ctx.zero_ext(&x, 32).unwrap();
        assert_eq!(zext.to_smtlib(), "((_ zero_extend 32) x)");

        let sext = ctx.sign_ext(&x, 32).unwrap();
        assert_eq!(sext.to_smtlib(), "((_ sign_extend 32) x)");
    }

    #[test]
    fn test_ite() {
        let ctx = Context::new();
        let cond = ctx.bools("c").unwrap();
        let x = ctx.bvs("x", 64).unwrap();
        let y = ctx.bvs("y", 64).unwrap();

        let ite = ctx.ite(&cond, &x, &y).unwrap();
        assert_eq!(ite.to_smtlib(), "(ite c x y)");
    }

    #[test]
    fn test_string_value() {
        let ctx = Context::new();
        let s = ctx.stringv("hello").unwrap();
        assert_eq!(s.to_smtlib(), "\"hello\"");
    }

    #[test]
    fn test_string_value_with_quotes() {
        let ctx = Context::new();
        let s = ctx.stringv("say \"hi\"").unwrap();
        assert_eq!(s.to_smtlib(), "\"say \\\"hi\\\"\"");
    }

    #[test]
    fn test_smtlib_display_wrapper() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 64).unwrap();
        let displayed = format!("{}", SmtLibDisplay(&x));
        assert_eq!(displayed, "x");
    }
}
