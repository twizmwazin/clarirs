use clarirs_core::prelude::*;
use cvc5_rs::{Kind, SortKind, Term, TermManager};

use super::AstExtCvc5;

pub(crate) fn to_cvc5(
    tm: &TermManager,
    ast: &BoolAst,
    children: &[Term],
) -> Result<Term, ClarirsError> {
    Ok(match ast.op() {
        BooleanOp::BoolS(s) => {
            let sort = tm.boolean_sort();
            tm.mk_const(sort, s.as_str())
        }
        BooleanOp::BoolV(b) => {
            if *b {
                tm.mk_true()
            } else {
                tm.mk_false()
            }
        }
        BooleanOp::Not(..) => {
            let a = children[0].clone();
            tm.mk_term(Kind::CVC5_KIND_NOT, &[a])
        }
        BooleanOp::And(..) => tm.mk_term(Kind::CVC5_KIND_AND, children),
        BooleanOp::Or(..) => tm.mk_term(Kind::CVC5_KIND_OR, children),
        BooleanOp::Xor(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_XOR, &[a, b])
        }
        BooleanOp::BoolEq(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_EQUAL, &[a, b])
        }
        BooleanOp::BoolNeq(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_DISTINCT, &[a, b])
        }
        BooleanOp::ITE(..) => {
            let cond = children[0].clone();
            let then = children[1].clone();
            let else_ = children[2].clone();
            tm.mk_term(Kind::CVC5_KIND_ITE, &[cond, then, else_])
        }

        // BV operations
        BooleanOp::Eq(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_EQUAL, &[a, b])
        }
        BooleanOp::Neq(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_DISTINCT, &[a, b])
        }
        BooleanOp::ULT(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_ULT, &[a, b])
        }
        BooleanOp::ULE(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_ULE, &[a, b])
        }
        BooleanOp::UGT(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_UGT, &[a, b])
        }
        BooleanOp::UGE(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_UGE, &[a, b])
        }
        BooleanOp::SLT(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_SLT, &[a, b])
        }
        BooleanOp::SLE(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_SLE, &[a, b])
        }
        BooleanOp::SGT(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_SGT, &[a, b])
        }
        BooleanOp::SGE(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_BITVECTOR_SGE, &[a, b])
        }

        // FP operations
        BooleanOp::FpEq(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_EQ, &[a, b])
        }
        BooleanOp::FpNeq(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            let eq = tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_EQ, &[a, b]);
            tm.mk_term(Kind::CVC5_KIND_NOT, &[eq])
        }
        BooleanOp::FpLt(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_LT, &[a, b])
        }
        BooleanOp::FpLeq(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_LEQ, &[a, b])
        }
        BooleanOp::FpGt(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_GT, &[a, b])
        }
        BooleanOp::FpGeq(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_GEQ, &[a, b])
        }
        BooleanOp::FpIsNan(..) => {
            let a = children[0].clone();
            tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_IS_NAN, &[a])
        }
        BooleanOp::FpIsInf(..) => {
            let a = children[0].clone();
            tm.mk_term(Kind::CVC5_KIND_FLOATINGPOINT_IS_INF, &[a])
        }

        // String operations
        BooleanOp::StrContains(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_STRING_CONTAINS, &[a, b])
        }
        BooleanOp::StrPrefixOf(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_STRING_PREFIX, &[a, b])
        }
        BooleanOp::StrSuffixOf(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_STRING_SUFFIX, &[a, b])
        }
        BooleanOp::StrIsDigit(..) => {
            let a = children[0].clone();
            tm.mk_term(Kind::CVC5_KIND_STRING_IS_DIGIT, &[a])
        }
        BooleanOp::StrEq(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_EQUAL, &[a, b])
        }
        BooleanOp::StrNeq(..) => {
            let a = children[0].clone();
            let b = children[1].clone();
            tm.mk_term(Kind::CVC5_KIND_DISTINCT, &[a, b])
        }
    })
}

pub(crate) fn from_cvc5<'c>(
    ctx: &'c Context<'c>,
    tm: &TermManager,
    term: &Term,
) -> Result<BoolAst<'c>, ClarirsError> {
    let sort = term.sort();
    if !sort.is_boolean() {
        return Err(ClarirsError::ConversionError(
            "expected a boolean term".to_string(),
        ));
    }

    let kind = term.kind();
    match kind {
        Kind::CVC5_KIND_CONST_BOOLEAN => {
            let val = term.boolean_value();
            if val {
                ctx.true_()
            } else {
                ctx.false_()
            }
        }
        Kind::CVC5_KIND_CONSTANT => {
            let name = term.symbol();
            ctx.bools(name)
        }
        Kind::CVC5_KIND_NOT => {
            let arg = term.child(0);
            let inner = BoolAst::from_cvc5(ctx, tm, &arg)?;
            if let BooleanOp::BoolEq(a, b) = inner.op() {
                ctx.neq(a, b)
            } else {
                ctx.not(inner)
            }
        }
        Kind::CVC5_KIND_AND => {
            let num = term.num_children();
            let mut args = Vec::with_capacity(num);
            for i in 0..num {
                let arg = term.child(i);
                args.push(BoolAst::from_cvc5(ctx, tm, &arg)?);
            }
            ctx.and(args)
        }
        Kind::CVC5_KIND_OR => {
            let num = term.num_children();
            let mut args = Vec::with_capacity(num);
            for i in 0..num {
                let arg = term.child(i);
                args.push(BoolAst::from_cvc5(ctx, tm, &arg)?);
            }
            ctx.or(args)
        }
        Kind::CVC5_KIND_XOR => {
            let a = BoolAst::from_cvc5(ctx, tm, &term.child(0))?;
            let b = BoolAst::from_cvc5(ctx, tm, &term.child(1))?;
            ctx.xor(a, b)
        }
        Kind::CVC5_KIND_EQUAL => {
            let arg0 = term.child(0);
            let arg1 = term.child(1);
            let arg_sort = arg0.sort();
            let sort_kind = arg_sort.kind();

            match sort_kind {
                SortKind::CVC5_SORT_KIND_BOOLEAN_SORT => {
                    let lhs = BoolAst::from_cvc5(ctx, tm, &arg0)?;
                    let rhs = BoolAst::from_cvc5(ctx, tm, &arg1)?;
                    ctx.eq_(lhs, rhs)
                }
                SortKind::CVC5_SORT_KIND_BITVECTOR_SORT => {
                    let lhs = BitVecAst::from_cvc5(ctx, tm, &arg0)?;
                    let rhs = BitVecAst::from_cvc5(ctx, tm, &arg1)?;
                    ctx.eq_(lhs, rhs)
                }
                SortKind::CVC5_SORT_KIND_FLOATINGPOINT_SORT => {
                    let lhs = FloatAst::from_cvc5(ctx, tm, &arg0)?;
                    let rhs = FloatAst::from_cvc5(ctx, tm, &arg1)?;
                    ctx.eq_(lhs, rhs)
                }
                SortKind::CVC5_SORT_KIND_STRING_SORT => {
                    let lhs = StringAst::from_cvc5(ctx, tm, &arg0)?;
                    let rhs = StringAst::from_cvc5(ctx, tm, &arg1)?;
                    ctx.str_eq(lhs, rhs)
                }
                _ => Err(ClarirsError::ConversionError(
                    "Eq operand has unrecognized sort".to_string(),
                )),
            }
        }
        Kind::CVC5_KIND_DISTINCT => {
            let num = term.num_children();
            if num != 2 {
                return Err(ClarirsError::ConversionError(
                    "Distinct with != 2 args not supported".to_string(),
                ));
            }
            let arg0 = term.child(0);
            let arg1 = term.child(1);
            let arg_sort = arg0.sort();
            let sort_kind = arg_sort.kind();

            match sort_kind {
                SortKind::CVC5_SORT_KIND_BOOLEAN_SORT => {
                    let lhs = BoolAst::from_cvc5(ctx, tm, &arg0)?;
                    let rhs = BoolAst::from_cvc5(ctx, tm, &arg1)?;
                    ctx.neq(lhs, rhs)
                }
                SortKind::CVC5_SORT_KIND_BITVECTOR_SORT => {
                    let lhs = BitVecAst::from_cvc5(ctx, tm, &arg0)?;
                    let rhs = BitVecAst::from_cvc5(ctx, tm, &arg1)?;
                    ctx.neq(lhs, rhs)
                }
                SortKind::CVC5_SORT_KIND_FLOATINGPOINT_SORT => {
                    let lhs = FloatAst::from_cvc5(ctx, tm, &arg0)?;
                    let rhs = FloatAst::from_cvc5(ctx, tm, &arg1)?;
                    ctx.fp_neq(lhs, rhs)
                }
                SortKind::CVC5_SORT_KIND_STRING_SORT => {
                    let lhs = StringAst::from_cvc5(ctx, tm, &arg0)?;
                    let rhs = StringAst::from_cvc5(ctx, tm, &arg1)?;
                    ctx.str_neq(lhs, rhs)
                }
                _ => Err(ClarirsError::ConversionError(
                    "Distinct operand has unrecognized sort".to_string(),
                )),
            }
        }
        Kind::CVC5_KIND_BITVECTOR_ULT
        | Kind::CVC5_KIND_BITVECTOR_ULE
        | Kind::CVC5_KIND_BITVECTOR_UGT
        | Kind::CVC5_KIND_BITVECTOR_UGE
        | Kind::CVC5_KIND_BITVECTOR_SLT
        | Kind::CVC5_KIND_BITVECTOR_SLE
        | Kind::CVC5_KIND_BITVECTOR_SGT
        | Kind::CVC5_KIND_BITVECTOR_SGE => {
            let a = BitVecAst::from_cvc5(ctx, tm, &term.child(0))?;
            let b = BitVecAst::from_cvc5(ctx, tm, &term.child(1))?;
            match kind {
                Kind::CVC5_KIND_BITVECTOR_ULT => ctx.ult(a, b),
                Kind::CVC5_KIND_BITVECTOR_ULE => ctx.ule(a, b),
                Kind::CVC5_KIND_BITVECTOR_UGT => ctx.ugt(a, b),
                Kind::CVC5_KIND_BITVECTOR_UGE => ctx.uge(a, b),
                Kind::CVC5_KIND_BITVECTOR_SLT => ctx.slt(a, b),
                Kind::CVC5_KIND_BITVECTOR_SLE => ctx.sle(a, b),
                Kind::CVC5_KIND_BITVECTOR_SGT => ctx.sgt(a, b),
                Kind::CVC5_KIND_BITVECTOR_SGE => ctx.sge(a, b),
                _ => unreachable!(),
            }
        }
        Kind::CVC5_KIND_FLOATINGPOINT_EQ
        | Kind::CVC5_KIND_FLOATINGPOINT_LT
        | Kind::CVC5_KIND_FLOATINGPOINT_LEQ
        | Kind::CVC5_KIND_FLOATINGPOINT_GT
        | Kind::CVC5_KIND_FLOATINGPOINT_GEQ => {
            let a = FloatAst::from_cvc5(ctx, tm, &term.child(0))?;
            let b = FloatAst::from_cvc5(ctx, tm, &term.child(1))?;
            match kind {
                Kind::CVC5_KIND_FLOATINGPOINT_EQ => ctx.fp_eq(a, b),
                Kind::CVC5_KIND_FLOATINGPOINT_LT => ctx.fp_lt(a, b),
                Kind::CVC5_KIND_FLOATINGPOINT_LEQ => ctx.fp_leq(a, b),
                Kind::CVC5_KIND_FLOATINGPOINT_GT => ctx.fp_gt(a, b),
                Kind::CVC5_KIND_FLOATINGPOINT_GEQ => ctx.fp_geq(a, b),
                _ => unreachable!(),
            }
        }
        Kind::CVC5_KIND_FLOATINGPOINT_IS_NAN => {
            let a = FloatAst::from_cvc5(ctx, tm, &term.child(0))?;
            ctx.fp_is_nan(a)
        }
        Kind::CVC5_KIND_FLOATINGPOINT_IS_INF => {
            let a = FloatAst::from_cvc5(ctx, tm, &term.child(0))?;
            ctx.fp_is_inf(a)
        }
        Kind::CVC5_KIND_STRING_CONTAINS => {
            let a = StringAst::from_cvc5(ctx, tm, &term.child(0))?;
            let b = StringAst::from_cvc5(ctx, tm, &term.child(1))?;
            ctx.str_contains(a, b)
        }
        Kind::CVC5_KIND_STRING_PREFIX => {
            let a = StringAst::from_cvc5(ctx, tm, &term.child(0))?;
            let b = StringAst::from_cvc5(ctx, tm, &term.child(1))?;
            ctx.str_prefix_of(a, b)
        }
        Kind::CVC5_KIND_STRING_SUFFIX => {
            let a = StringAst::from_cvc5(ctx, tm, &term.child(0))?;
            let b = StringAst::from_cvc5(ctx, tm, &term.child(1))?;
            ctx.str_suffix_of(a, b)
        }
        Kind::CVC5_KIND_STRING_IS_DIGIT => {
            let a = StringAst::from_cvc5(ctx, tm, &term.child(0))?;
            ctx.str_is_digit(a)
        }
        Kind::CVC5_KIND_ITE => {
            let cond = BoolAst::from_cvc5(ctx, tm, &term.child(0))?;
            let then = BoolAst::from_cvc5(ctx, tm, &term.child(1))?;
            let else_ = BoolAst::from_cvc5(ctx, tm, &term.child(2))?;
            ctx.ite(cond, then, else_)
        }
        _ => Err(ClarirsError::ConversionError(format!(
            "Failed converting from cvc5: unknown kind for bool: {:?}",
            kind
        ))),
    }
}
