use std::collections::HashMap;
use std::fmt;

use crate::prelude::*;

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

fn to_smtlib_node(ast: &AstRef<'_>, children: &[String]) -> String {
    match ast.op() {
        // === Leaf nodes ===
        AstOp::BoolS(s) => s.to_string(),
        AstOp::BoolV(b) => b.to_string(),
        AstOp::BVS(s, _) => s.to_string(),
        AstOp::BVV(bit_vec) => format!("(_ bv{} {})", bit_vec.to_biguint(), bit_vec.len()),
        AstOp::FPS(s, _) => s.to_string(),
        AstOp::FPV(float) => {
            let sign = if float.sign() { "#b1" } else { "#b0" };
            let exp = float.exponent();
            let sig = float.mantissa();
            let exp_str = format!("{:0>width$b}", exp.to_biguint(), width = exp.len() as usize);
            let sig_str = format!("{:0>width$b}", sig.to_biguint(), width = sig.len() as usize);
            format!("(fp {sign} #b{exp_str} #b{sig_str})")
        }
        AstOp::StringS(s) => s.to_string(),
        AstOp::StringV(s) => format!("\"{}\"", s.replace('"', "\\\"")),

        // === Cross-sort operations ===
        AstOp::Not(child) => {
            // Check if this is a boolean not or a bitvec not
            if child.op().base_theories() == Theories::BITVEC {
                format!("(bvnot {})", children[0])
            } else {
                format!("(not {})", children[0])
            }
        }
        AstOp::And(args) => {
            if !args.is_empty() && args[0].op().base_theories() == Theories::BITVEC {
                format!(
                    "(bvand{})",
                    children
                        .iter()
                        .fold(String::new(), |acc, c| format!("{} {}", acc, c))
                )
            } else {
                format!("(and {})", children.join(" "))
            }
        }
        AstOp::Or(args) => {
            if !args.is_empty() && args[0].op().base_theories() == Theories::BITVEC {
                format!(
                    "(bvor{})",
                    children
                        .iter()
                        .fold(String::new(), |acc, c| format!("{} {}", acc, c))
                )
            } else {
                format!("(or {})", children.join(" "))
            }
        }
        AstOp::Xor(args) => {
            if !args.is_empty() && args[0].op().base_theories() == Theories::BITVEC {
                format!(
                    "(bvxor{})",
                    children
                        .iter()
                        .fold(String::new(), |acc, c| format!("{} {}", acc, c))
                )
            } else {
                format!("(xor {} {})", children[0], children[1])
            }
        }
        AstOp::Eq(lhs, _) => {
            // Check the theory of children to determine the right representation
            let theory = lhs.op().base_theories();
            if theory == Theories::FLOAT {
                format!("(fp.eq {} {})", children[0], children[1])
            } else {
                format!("(= {} {})", children[0], children[1])
            }
        }
        AstOp::Neq(lhs, _) => {
            let theory = lhs.op().base_theories();
            if theory == Theories::FLOAT {
                format!("(not (fp.eq {} {}))", children[0], children[1])
            } else if theory == Theories::STRING {
                format!("(not (= {} {}))", children[0], children[1])
            } else {
                format!("(distinct {} {})", children[0], children[1])
            }
        }
        AstOp::If(..) => format!("(ite {} {} {})", children[0], children[1], children[2]),

        // === BV arithmetic ===
        AstOp::Neg(..) => format!("(bvneg {})", children[0]),
        AstOp::Add(..) => format!(
            "(bvadd{})",
            children
                .iter()
                .fold(String::new(), |acc, c| format!("{} {}", acc, c))
        ),
        AstOp::Sub(..) => format!("(bvsub {} {})", children[0], children[1]),
        AstOp::Mul(..) => format!(
            "(bvmul{})",
            children
                .iter()
                .fold(String::new(), |acc, c| format!("{} {}", acc, c))
        ),
        AstOp::UDiv(..) => format!("(bvudiv {} {})", children[0], children[1]),
        AstOp::SDiv(..) => format!("(bvsdiv {} {})", children[0], children[1]),
        AstOp::URem(..) => format!("(bvurem {} {})", children[0], children[1]),
        AstOp::SRem(..) => format!("(bvsrem {} {})", children[0], children[1]),

        // === BV shifts/rotates ===
        AstOp::ShL(..) => format!("(bvshl {} {})", children[0], children[1]),
        AstOp::LShR(..) => format!("(bvlshr {} {})", children[0], children[1]),
        AstOp::AShR(..) => format!("(bvashr {} {})", children[0], children[1]),
        AstOp::RotateLeft(..) => {
            format!("(ext_rotate_left {} {})", children[0], children[1])
        }
        AstOp::RotateRight(..) => {
            format!("(ext_rotate_right {} {})", children[0], children[1])
        }

        // === BV extraction/extension ===
        AstOp::Extract(_, high, low) => {
            format!("((_ extract {} {}) {})", high, low, children[0])
        }
        AstOp::ZeroExt(_, size) => format!("((_ zero_extend {}) {})", size, children[0]),
        AstOp::SignExt(_, size) => format!("((_ sign_extend {}) {})", size, children[0]),
        AstOp::Concat(..) => format!("(concat {})", children.join(" ")),
        AstOp::ByteReverse(..) => format!("(bvreverse {})", children[0]),

        // === BV comparisons ===
        AstOp::ULT(..) => format!("(bvult {} {})", children[0], children[1]),
        AstOp::ULE(..) => format!("(bvule {} {})", children[0], children[1]),
        AstOp::UGT(..) => format!("(bvugt {} {})", children[0], children[1]),
        AstOp::UGE(..) => format!("(bvuge {} {})", children[0], children[1]),
        AstOp::SLT(..) => format!("(bvslt {} {})", children[0], children[1]),
        AstOp::SLE(..) => format!("(bvsle {} {})", children[0], children[1]),
        AstOp::SGT(..) => format!("(bvsgt {} {})", children[0], children[1]),
        AstOp::SGE(..) => format!("(bvsge {} {})", children[0], children[1]),

        // === Float operations ===
        AstOp::FpFP(..) => format!("(fp {} {} {})", children[0], children[1], children[2]),
        AstOp::FpNeg(..) => format!("(fp.neg {})", children[0]),
        AstOp::FpAbs(..) => format!("(fp.abs {})", children[0]),
        AstOp::FpAdd(_, _, fprm) => format!(
            "(fp.add {} {} {})",
            fprm_to_smtlib(fprm),
            children[0],
            children[1]
        ),
        AstOp::FpSub(_, _, fprm) => format!(
            "(fp.sub {} {} {})",
            fprm_to_smtlib(fprm),
            children[0],
            children[1]
        ),
        AstOp::FpMul(_, _, fprm) => format!(
            "(fp.mul {} {} {})",
            fprm_to_smtlib(fprm),
            children[0],
            children[1]
        ),
        AstOp::FpDiv(_, _, fprm) => format!(
            "(fp.div {} {} {})",
            fprm_to_smtlib(fprm),
            children[0],
            children[1]
        ),
        AstOp::FpSqrt(_, fprm) => format!("(fp.sqrt {} {})", fprm_to_smtlib(fprm), children[0]),
        AstOp::FpToFp(_, fsort, fprm) => format!(
            "((_ to_fp {} {}) {} {})",
            fsort.exponent,
            fsort.mantissa,
            fprm_to_smtlib(fprm),
            children[0]
        ),
        AstOp::BvToFp(_, fsort) => format!(
            "((_ to_fp {} {}) {})",
            fsort.exponent, fsort.mantissa, children[0]
        ),
        AstOp::BvToFpSigned(_, fsort, fprm) => format!(
            "((_ to_fp {} {}) {} {})",
            fsort.exponent,
            fsort.mantissa,
            fprm_to_smtlib(fprm),
            children[0]
        ),
        AstOp::BvToFpUnsigned(_, fsort, fprm) => format!(
            "((_ to_fp_unsigned {} {}) {} {})",
            fsort.exponent,
            fsort.mantissa,
            fprm_to_smtlib(fprm),
            children[0]
        ),

        // === Float comparisons ===
        AstOp::FpLt(..) => format!("(fp.lt {} {})", children[0], children[1]),
        AstOp::FpLeq(..) => format!("(fp.leq {} {})", children[0], children[1]),
        AstOp::FpGt(..) => format!("(fp.gt {} {})", children[0], children[1]),
        AstOp::FpGeq(..) => format!("(fp.geq {} {})", children[0], children[1]),
        AstOp::FpIsNan(..) => format!("(fp.isNaN {})", children[0]),
        AstOp::FpIsInf(..) => format!("(fp.isInfinite {})", children[0]),

        // === Float-BV conversions ===
        AstOp::FpToIEEEBV(..) => format!("(fp.to_ieee_bv {})", children[0]),
        AstOp::FpToUBV(_, size, fprm) => format!(
            "((_ fp.to_ubv {}) {} {})",
            size,
            fprm_to_smtlib(fprm),
            children[0]
        ),
        AstOp::FpToSBV(_, size, fprm) => format!(
            "((_ fp.to_sbv {}) {} {})",
            size,
            fprm_to_smtlib(fprm),
            children[0]
        ),

        // === String operations ===
        AstOp::StrConcat(..) => format!("(str.++ {} {})", children[0], children[1]),
        AstOp::StrSubstr(..) => format!(
            "(str.substr {} {} {})",
            children[0], children[1], children[2]
        ),
        AstOp::StrReplace(..) => format!(
            "(str.replace {} {} {})",
            children[0], children[1], children[2]
        ),
        AstOp::BVToStr(..) => format!("(str.from_bv {})", children[0]),
        AstOp::StrLen(..) => format!("(str.len {})", children[0]),
        AstOp::StrIndexOf(..) => {
            format!(
                "(str.indexof {} {} {})",
                children[0], children[1], children[2]
            )
        }
        AstOp::StrToBV(..) => format!("(str.to_bv {})", children[0]),

        // === String comparisons ===
        AstOp::StrContains(..) => format!("(str.contains {} {})", children[0], children[1]),
        AstOp::StrPrefixOf(..) => format!("(str.prefixof {} {})", children[0], children[1]),
        AstOp::StrSuffixOf(..) => format!("(str.suffixof {} {})", children[0], children[1]),
        AstOp::StrIsDigit(..) => format!("(str.is_digit {})", children[0]),

        // === VSA operations ===
        AstOp::Union(..) => format!("(vsaunion {} {})", children[0], children[1]),
        AstOp::Intersection(..) => {
            format!("(vsaintersection {} {})", children[0], children[1])
        }
        AstOp::Widen(..) => format!("(vsawiden {} {})", children[0], children[1]),
    }
}

/// Iterative post-order traversal for SMT-LIB conversion.
fn to_smtlib_impl(ast: &AstRef<'_>) -> String {
    use std::collections::VecDeque;

    struct NodeState<'c> {
        node: AstRef<'c>,
        children_processed: usize,
        num_children: usize,
        child_results: Vec<String>,
    }

    let mut cache: HashMap<u64, String> = HashMap::new();
    let mut stack = Vec::new();
    let mut result_queue = VecDeque::new();

    let num_children = ast.num_children();
    stack.push(NodeState {
        node: ast.clone(),
        children_processed: 0,
        num_children,
        child_results: Vec::new(),
    });

    while let Some(mut state) = stack.pop() {
        // Check cache
        if let Some(cached) = cache.get(&state.node.hash()) {
            result_queue.push_back(cached.clone());
            // If we just finished processing a child, add its result to its parent
            if let Some(parent) = stack.last_mut() {
                if parent.children_processed > 0 && !result_queue.is_empty() {
                    parent.child_results.push(result_queue.pop_front().unwrap());
                }
            }
            continue;
        }

        if state.children_processed == state.num_children {
            // All children processed, process this node
            let result = to_smtlib_node(&state.node, &state.child_results);
            cache.insert(state.node.hash(), result.clone());
            result_queue.push_back(result);
        } else {
            // Process next child
            let child = state.node.get_child(state.children_processed).unwrap();
            state.children_processed += 1;

            // Push parent back on stack
            stack.push(state);

            // Push child on stack
            let num_children = child.num_children();
            stack.push(NodeState {
                node: child,
                children_processed: 0,
                num_children,
                child_results: Vec::new(),
            });
            continue;
        }

        // If we just finished processing a child, add its result to its parent
        if !result_queue.is_empty()
            && !stack.is_empty()
        {
            if let Some(parent) = stack.last_mut() {
                if parent.children_processed > 0 {
                    parent.child_results.push(result_queue.pop_front().unwrap());
                }
            }
        }
    }

    result_queue.pop_front().unwrap_or_default()
}

/// Trait for converting an AST to an SMT-LIB 2.6 string representation.
pub trait ToSmtLib {
    fn to_smtlib(&self) -> String;
}

impl ToSmtLib for AstRef<'_> {
    fn to_smtlib(&self) -> String {
        to_smtlib_impl(self)
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
