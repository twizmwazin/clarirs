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

fn to_smtlib_node(ast: &AstRef, children: &[String]) -> String {
    match ast.op() {
        // ── Boolean ops ─────────────────────────────────────────────
        Op::BoolS(s) => s.to_string(),
        Op::BoolV(b) => b.to_string(),
        Op::Not(..) => format!("(not {})", children[0]),
        Op::And(..) => format!("(and {})", children.join(" ")),
        Op::Or(..) => format!("(or {})", children.join(" ")),
        Op::Xor(..) => format!("(xor {} {})", children[0], children[1]),
        Op::Eq(..) => format!("(= {} {})", children[0], children[1]),
        Op::Distinct(..) => format!("(distinct {} {})", children[0], children[1]),
        Op::ULT(..) => format!("(bvult {} {})", children[0], children[1]),
        Op::ULE(..) => format!("(bvule {} {})", children[0], children[1]),
        Op::UGT(..) => format!("(bvugt {} {})", children[0], children[1]),
        Op::UGE(..) => format!("(bvuge {} {})", children[0], children[1]),
        Op::SLT(..) => format!("(bvslt {} {})", children[0], children[1]),
        Op::SLE(..) => format!("(bvsle {} {})", children[0], children[1]),
        Op::SGT(..) => format!("(bvsgt {} {})", children[0], children[1]),
        Op::SGE(..) => format!("(bvsge {} {})", children[0], children[1]),
        Op::FpEq(..) => format!("(fp.eq {} {})", children[0], children[1]),
        Op::FpNeq(..) => format!("(not (fp.eq {} {}))", children[0], children[1]),
        Op::FpLt(..) => format!("(fp.lt {} {})", children[0], children[1]),
        Op::FpLeq(..) => format!("(fp.leq {} {})", children[0], children[1]),
        Op::FpGt(..) => format!("(fp.gt {} {})", children[0], children[1]),
        Op::FpGeq(..) => format!("(fp.geq {} {})", children[0], children[1]),
        Op::FpIsNan(..) => format!("(fp.isNaN {})", children[0]),
        Op::FpIsInf(..) => format!("(fp.isInfinite {})", children[0]),
        Op::StrContains(..) => format!("(str.contains {} {})", children[0], children[1]),
        Op::StrPrefixOf(..) => format!("(str.prefixof {} {})", children[0], children[1]),
        Op::StrSuffixOf(..) => format!("(str.suffixof {} {})", children[0], children[1]),
        Op::StrIsDigit(..) => format!("(str.is_digit {})", children[0]),
        Op::ITE(..) => format!("(ite {} {} {})", children[0], children[1], children[2]),

        // ── BitVec ops ──────────────────────────────────────────────
        Op::BVS(s, _) => s.to_string(),
        Op::BVV(bit_vec) => format!("(_ bv{} {})", bit_vec.to_biguint(), bit_vec.len()),
        Op::BVNot(..) => format!("(bvnot {})", children[0]),
        Op::BVAnd(..) => format!(
            "(bvand{})",
            children
                .iter()
                .fold(String::new(), |acc, c| format!("{} {}", acc, c))
        ),
        Op::BVOr(..) => format!(
            "(bvor{})",
            children
                .iter()
                .fold(String::new(), |acc, c| format!("{} {}", acc, c))
        ),
        Op::BVXor(..) => format!(
            "(bvxor{})",
            children
                .iter()
                .fold(String::new(), |acc, c| format!("{} {}", acc, c))
        ),
        Op::Neg(..) => format!("(bvneg {})", children[0]),
        Op::Add(..) => format!(
            "(bvadd{})",
            children
                .iter()
                .fold(String::new(), |acc, c| format!("{} {}", acc, c))
        ),
        Op::Sub(..) => format!("(bvsub {} {})", children[0], children[1]),
        Op::Mul(..) => format!(
            "(bvmul{})",
            children
                .iter()
                .fold(String::new(), |acc, c| format!("{} {}", acc, c))
        ),
        Op::UDiv(..) => format!("(bvudiv {} {})", children[0], children[1]),
        Op::SDiv(..) => format!("(bvsdiv {} {})", children[0], children[1]),
        Op::URem(..) => format!("(bvurem {} {})", children[0], children[1]),
        Op::SRem(..) => format!("(bvsrem {} {})", children[0], children[1]),
        Op::ShL(..) => format!("(bvshl {} {})", children[0], children[1]),
        Op::LShR(..) => format!("(bvlshr {} {})", children[0], children[1]),
        Op::AShR(..) => format!("(bvashr {} {})", children[0], children[1]),
        Op::RotateLeft(..) => {
            format!("(ext_rotate_left {} {})", children[0], children[1])
        }
        Op::RotateRight(..) => {
            format!("(ext_rotate_right {} {})", children[0], children[1])
        }
        Op::ZeroExt(_, size) => format!("((_ zero_extend {}) {})", size, children[0]),
        Op::SignExt(_, size) => format!("((_ sign_extend {}) {})", size, children[0]),
        Op::Extract(_, high, low) => {
            format!("((_ extract {} {}) {})", high, low, children[0])
        }
        Op::Concat(..) => format!("(concat {})", children.join(" ")),
        Op::ByteReverse(..) => format!("(bvreverse {})", children[0]),
        Op::FpToIEEEBV(..) => format!("(fp.to_ieee_bv {})", children[0]),
        Op::FpToUBV(_, size, fprm) => format!(
            "((_ fp.to_ubv {}) {} {})",
            size,
            fprm_to_smtlib(fprm),
            children[0]
        ),
        Op::FpToSBV(_, size, fprm) => format!(
            "((_ fp.to_sbv {}) {} {})",
            size,
            fprm_to_smtlib(fprm),
            children[0]
        ),
        Op::StrLen(..) => format!("(str.len {})", children[0]),
        Op::StrIndexOf(..) => {
            format!(
                "(str.indexof {} {} {})",
                children[0], children[1], children[2]
            )
        }
        Op::StrToBV(..) => format!("(str.to_bv {})", children[0]),
        Op::Union(..) => format!("(vsaunion {} {})", children[0], children[1]),
        Op::Intersection(..) => {
            format!("(vsaintersection {} {})", children[0], children[1])
        }
        Op::Widen(..) => format!("(vsawiden {} {})", children[0], children[1]),

        // ── Float ops ───────────────────────────────────────────────
        Op::FPS(s, _) => s.to_string(),
        Op::FPV(float) => {
            let sign = if float.sign() { "#b1" } else { "#b0" };
            let exp = float.exponent();
            let sig = float.mantissa();
            let exp_str = format!("{:0>width$b}", exp.to_biguint(), width = exp.len() as usize);
            let sig_str = format!("{:0>width$b}", sig.to_biguint(), width = sig.len() as usize);
            format!("(fp {sign} #b{exp_str} #b{sig_str})")
        }
        Op::FpFP(..) => format!("(fp {} {} {})", children[0], children[1], children[2]),
        Op::FpNeg(..) => format!("(fp.neg {})", children[0]),
        Op::FpAbs(..) => format!("(fp.abs {})", children[0]),
        Op::FpAdd(_, _, fprm) => format!(
            "(fp.add {} {} {})",
            fprm_to_smtlib(fprm),
            children[0],
            children[1]
        ),
        Op::FpSub(_, _, fprm) => format!(
            "(fp.sub {} {} {})",
            fprm_to_smtlib(fprm),
            children[0],
            children[1]
        ),
        Op::FpMul(_, _, fprm) => format!(
            "(fp.mul {} {} {})",
            fprm_to_smtlib(fprm),
            children[0],
            children[1]
        ),
        Op::FpDiv(_, _, fprm) => format!(
            "(fp.div {} {} {})",
            fprm_to_smtlib(fprm),
            children[0],
            children[1]
        ),
        Op::FpSqrt(_, fprm) => format!("(fp.sqrt {} {})", fprm_to_smtlib(fprm), children[0]),
        Op::FpToFp(_, fsort, fprm) => format!(
            "((_ to_fp {} {}) {} {})",
            fsort.exponent,
            fsort.mantissa,
            fprm_to_smtlib(fprm),
            children[0]
        ),
        Op::BvToFp(_, fsort) => format!(
            "((_ to_fp {} {}) {})",
            fsort.exponent, fsort.mantissa, children[0]
        ),
        Op::BvToFpSigned(_, fsort, fprm) => format!(
            "((_ to_fp {} {}) {} {})",
            fsort.exponent,
            fsort.mantissa,
            fprm_to_smtlib(fprm),
            children[0]
        ),
        Op::BvToFpUnsigned(_, fsort, fprm) => format!(
            "((_ to_fp_unsigned {} {}) {} {})",
            fsort.exponent,
            fsort.mantissa,
            fprm_to_smtlib(fprm),
            children[0]
        ),
        // ── String ops ──────────────────────────────────────────────
        Op::StringS(s) => s.to_string(),
        Op::StringV(s) => format!("\"{}\"", s.replace('"', "\\\"")),
        Op::StrConcat(..) => format!("(str.++ {} {})", children[0], children[1]),
        Op::StrSubstr(..) => format!(
            "(str.substr {} {} {})",
            children[0], children[1], children[2]
        ),
        Op::StrReplace(..) => format!(
            "(str.replace {} {} {})",
            children[0], children[1], children[2]
        ),
        Op::BVToStr(..) => format!("(str.from_bv {})", children[0]),
    }
}

/// Trait for converting an AST to an SMT-LIB 2.6 string representation.
pub trait ToSmtLib {
    fn to_smtlib(&self) -> String;
}

impl ToSmtLib for AstRef<'_> {
    fn to_smtlib(&self) -> String {
        walk_post_order(
            self.clone(),
            |node, children| Ok(to_smtlib_node(&node, children)),
            &(),
        )
        .expect("infallible")
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
