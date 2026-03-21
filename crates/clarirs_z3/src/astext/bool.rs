use crate::astext::child;
use clarirs_core::prelude::*;
use z3::ast::{Ast, Bool, Dynamic};

use super::AstExtZ3;

pub(crate) fn to_z3(
    ast: &BoolAst,
    children: &[Dynamic],
) -> Result<Dynamic, ClarirsError> {
    Ok(match ast.op() {
        BooleanOp::BoolS(s) => {
            Dynamic::from(Bool::new_const(s.as_str()))
        }
        BooleanOp::BoolV(b) => {
            Dynamic::from(Bool::from_bool(*b))
        }
        BooleanOp::Not(..) => {
            let a = child(children, 0)?.as_bool().unwrap();
            Dynamic::from(a.not())
        }
        BooleanOp::And(..) => {
            let args: Vec<Bool> = children.iter().map(|c| c.as_bool().unwrap()).collect();
            let refs: Vec<&Bool> = args.iter().collect();
            Dynamic::from(Bool::and(&refs))
        }
        BooleanOp::Or(..) => {
            let args: Vec<Bool> = children.iter().map(|c| c.as_bool().unwrap()).collect();
            let refs: Vec<&Bool> = args.iter().collect();
            Dynamic::from(Bool::or(&refs))
        }
        BooleanOp::Xor(..) => {
            let a = child(children, 0)?.as_bool().unwrap();
            let b = child(children, 1)?.as_bool().unwrap();
            Dynamic::from(a.xor(&b))
        }
        BooleanOp::BoolEq(..) => {
            let a = child(children, 0)?;
            let b = child(children, 1)?;
            Dynamic::from(a.eq(b))
        }
        BooleanOp::BoolNeq(..) => {
            let a = child(children, 0)?;
            let b = child(children, 1)?;
            Dynamic::from(Dynamic::distinct(&[a, b]))
        }
        BooleanOp::ITE(..) => {
            let cond = child(children, 0)?.as_bool().unwrap();
            let then = child(children, 1)?;
            let else_ = child(children, 2)?;
            cond.ite(then, else_)
        }

        // BV comparisons
        BooleanOp::Eq(..) => {
            let a = child(children, 0)?;
            let b = child(children, 1)?;
            Dynamic::from(a.eq(b))
        }
        BooleanOp::Neq(..) => {
            let a = child(children, 0)?;
            let b = child(children, 1)?;
            Dynamic::from(Dynamic::distinct(&[a, b]))
        }
        BooleanOp::ULT(..) => {
            let a = child(children, 0)?.as_bv().unwrap();
            let b = child(children, 1)?.as_bv().unwrap();
            Dynamic::from(a.bvult(&b))
        }
        BooleanOp::ULE(..) => {
            let a = child(children, 0)?.as_bv().unwrap();
            let b = child(children, 1)?.as_bv().unwrap();
            Dynamic::from(a.bvule(&b))
        }
        BooleanOp::UGT(..) => {
            let a = child(children, 0)?.as_bv().unwrap();
            let b = child(children, 1)?.as_bv().unwrap();
            Dynamic::from(a.bvugt(&b))
        }
        BooleanOp::UGE(..) => {
            let a = child(children, 0)?.as_bv().unwrap();
            let b = child(children, 1)?.as_bv().unwrap();
            Dynamic::from(a.bvuge(&b))
        }
        BooleanOp::SLT(..) => {
            let a = child(children, 0)?.as_bv().unwrap();
            let b = child(children, 1)?.as_bv().unwrap();
            Dynamic::from(a.bvslt(&b))
        }
        BooleanOp::SLE(..) => {
            let a = child(children, 0)?.as_bv().unwrap();
            let b = child(children, 1)?.as_bv().unwrap();
            Dynamic::from(a.bvsle(&b))
        }
        BooleanOp::SGT(..) => {
            let a = child(children, 0)?.as_bv().unwrap();
            let b = child(children, 1)?.as_bv().unwrap();
            Dynamic::from(a.bvsgt(&b))
        }
        BooleanOp::SGE(..) => {
            let a = child(children, 0)?.as_bv().unwrap();
            let b = child(children, 1)?.as_bv().unwrap();
            Dynamic::from(a.bvsge(&b))
        }

        // FP comparisons
        BooleanOp::FpEq(..) => {
            let a = child(children, 0)?.as_float().unwrap();
            let b = child(children, 1)?.as_float().unwrap();
            Dynamic::from(a.eq_fpa(&b))
        }
        BooleanOp::FpNeq(..) => {
            let a = child(children, 0)?;
            let b = child(children, 1)?;
            Dynamic::from(Dynamic::distinct(&[a, b]))
        }
        BooleanOp::FpLt(..) => {
            let a = child(children, 0)?.as_float().unwrap();
            let b = child(children, 1)?.as_float().unwrap();
            Dynamic::from(a.lt(&b))
        }
        BooleanOp::FpLeq(..) => {
            let a = child(children, 0)?.as_float().unwrap();
            let b = child(children, 1)?.as_float().unwrap();
            Dynamic::from(a.le(&b))
        }
        BooleanOp::FpGt(..) => {
            let a = child(children, 0)?.as_float().unwrap();
            let b = child(children, 1)?.as_float().unwrap();
            Dynamic::from(a.gt(&b))
        }
        BooleanOp::FpGeq(..) => {
            let a = child(children, 0)?.as_float().unwrap();
            let b = child(children, 1)?.as_float().unwrap();
            Dynamic::from(a.ge(&b))
        }
        BooleanOp::FpIsNan(..) => {
            let a = child(children, 0)?.as_float().unwrap();
            Dynamic::from(a.is_nan())
        }
        BooleanOp::FpIsInf(..) => {
            let a = child(children, 0)?.as_float().unwrap();
            Dynamic::from(a.is_infinite())
        }

        // String comparisons
        BooleanOp::StrContains(..) => {
            let a = child(children, 0)?.as_string().unwrap();
            let b = child(children, 1)?.as_string().unwrap();
            Dynamic::from(a.contains(&b))
        }
        BooleanOp::StrPrefixOf(..) => {
            let a = child(children, 0)?.as_string().unwrap();
            let b = child(children, 1)?.as_string().unwrap();
            Dynamic::from(a.prefix(&b))
        }
        BooleanOp::StrSuffixOf(..) => {
            let a = child(children, 0)?.as_string().unwrap();
            let b = child(children, 1)?.as_string().unwrap();
            Dynamic::from(a.suffix(&b))
        }
        BooleanOp::StrIsDigit(..) => {
            let a = child(children, 0)?.as_string().unwrap();
            // str.to_int returns -1 for non-digit strings, so >= 0 means all digits
            let int_val = super::string::str_to_int(&a);
            let zero = z3::ast::Int::from_i64(0);
            let is_non_negative = int_val.ge(&zero);
            // Also require non-empty string
            let str_len = a.length();
            let zero_int = z3::ast::Int::from_i64(0);
            let is_non_empty = str_len.gt(&zero_int);
            Dynamic::from(Bool::and(&[&is_non_negative, &is_non_empty]))
        }
        BooleanOp::StrEq(..) => {
            let a = child(children, 0)?;
            let b = child(children, 1)?;
            Dynamic::from(a.eq(b))
        }
        BooleanOp::StrNeq(..) => {
            let a = child(children, 0)?;
            let b = child(children, 1)?;
            Dynamic::from(Dynamic::distinct(&[a, b]))
        }
    })
}

pub(crate) fn from_z3<'c>(
    ctx: &'c Context<'c>,
    ast: Dynamic,
) -> Result<BoolAst<'c>, ClarirsError> {
    let ast_kind = ast.kind();
    match ast_kind {
        z3::AstKind::App => {
            let decl = ast.safe_decl().map_err(|_| {
                ClarirsError::ConversionError("not an app".to_string())
            })?;
            let decl_kind = decl.kind();

            match decl_kind {
                z3::DeclKind::TRUE => ctx.true_(),
                z3::DeclKind::FALSE => ctx.false_(),
                z3::DeclKind::NOT => {
                    let arg = ast.nth_child(0).unwrap();
                    let inner = BoolAst::from_z3(ctx, arg)?;

                    if let BooleanOp::BoolEq(a, b) = inner.op() {
                        ctx.neq(a, b)
                    } else {
                        ctx.not(inner)
                    }
                }
                z3::DeclKind::AND | z3::DeclKind::OR => {
                    let num_args = ast.num_children();
                    let mut args = Vec::with_capacity(num_args);
                    for i in 0..num_args {
                        let arg = ast.nth_child(i).unwrap();
                        args.push(BoolAst::from_z3(ctx, arg)?);
                    }
                    match decl_kind {
                        z3::DeclKind::AND => ctx.and(args),
                        z3::DeclKind::OR => ctx.or(args),
                        _ => unreachable!(),
                    }
                }
                z3::DeclKind::XOR => {
                    let a = BoolAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let b = BoolAst::from_z3(ctx, ast.nth_child(1).unwrap())?;
                    ctx.xor(a, b)
                }
                z3::DeclKind::EQ => {
                    let arg0 = ast.nth_child(0).unwrap();
                    let arg1 = ast.nth_child(1).unwrap();
                    let sort_kind = arg0.sort_kind();

                    match sort_kind {
                        z3::SortKind::Bool => {
                            let lhs = BoolAst::from_z3(ctx, arg0)?;
                            let rhs = BoolAst::from_z3(ctx, arg1)?;
                            ctx.eq_(lhs, rhs)
                        }
                        z3::SortKind::BV => {
                            let lhs = BitVecAst::from_z3(ctx, arg0)?;
                            let rhs = BitVecAst::from_z3(ctx, arg1)?;
                            ctx.eq_(lhs, rhs)
                        }
                        z3::SortKind::FloatingPoint => {
                            let lhs = FloatAst::from_z3(ctx, arg0)?;
                            let rhs = FloatAst::from_z3(ctx, arg1)?;
                            ctx.eq_(lhs, rhs)
                        }
                        z3::SortKind::Seq => {
                            let lhs = StringAst::from_z3(ctx, arg0)?;
                            let rhs = StringAst::from_z3(ctx, arg1)?;
                            ctx.str_eq(lhs, rhs)
                        }
                        _ => Err(ClarirsError::ConversionError(
                            "Eq operand has unrecognized sort".to_string(),
                        )),
                    }
                }
                z3::DeclKind::DISTINCT => {
                    if ast.num_children() != 2 {
                        return Err(ClarirsError::ConversionError(
                            "Distinct with != 2 args not supported".to_string(),
                        ));
                    }
                    let arg0 = ast.nth_child(0).unwrap();
                    let arg1 = ast.nth_child(1).unwrap();
                    let sort_kind = arg0.sort_kind();

                    match sort_kind {
                        z3::SortKind::Bool => {
                            let lhs = BoolAst::from_z3(ctx, arg0)?;
                            let rhs = BoolAst::from_z3(ctx, arg1)?;
                            ctx.neq(lhs, rhs)
                        }
                        z3::SortKind::BV => {
                            let lhs = BitVecAst::from_z3(ctx, arg0)?;
                            let rhs = BitVecAst::from_z3(ctx, arg1)?;
                            ctx.neq(lhs, rhs)
                        }
                        z3::SortKind::FloatingPoint => {
                            let lhs = FloatAst::from_z3(ctx, arg0)?;
                            let rhs = FloatAst::from_z3(ctx, arg1)?;
                            ctx.fp_neq(lhs, rhs)
                        }
                        z3::SortKind::Seq => {
                            let lhs = StringAst::from_z3(ctx, arg0)?;
                            let rhs = StringAst::from_z3(ctx, arg1)?;
                            ctx.str_neq(lhs, rhs)
                        }
                        _ => Err(ClarirsError::ConversionError(
                            "Distinct operand has unrecognized sort".to_string(),
                        )),
                    }
                }
                z3::DeclKind::ULT
                | z3::DeclKind::ULEQ
                | z3::DeclKind::UGT
                | z3::DeclKind::UGEQ
                | z3::DeclKind::SLT
                | z3::DeclKind::SLEQ
                | z3::DeclKind::SGT
                | z3::DeclKind::SGEQ => {
                    let a = BitVecAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let b = BitVecAst::from_z3(ctx, ast.nth_child(1).unwrap())?;

                    match decl_kind {
                        z3::DeclKind::ULT => ctx.ult(a, b),
                        z3::DeclKind::ULEQ => ctx.ule(a, b),
                        z3::DeclKind::UGT => ctx.ugt(a, b),
                        z3::DeclKind::UGEQ => ctx.uge(a, b),
                        z3::DeclKind::SLT => ctx.slt(a, b),
                        z3::DeclKind::SLEQ => ctx.sle(a, b),
                        z3::DeclKind::SGT => ctx.sgt(a, b),
                        z3::DeclKind::SGEQ => ctx.sge(a, b),
                        _ => unreachable!(),
                    }
                }
                z3::DeclKind::FPA_EQ
                | z3::DeclKind::FPA_LT
                | z3::DeclKind::FPA_LE
                | z3::DeclKind::FPA_GT
                | z3::DeclKind::FPA_GE => {
                    let a = FloatAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let b = FloatAst::from_z3(ctx, ast.nth_child(1).unwrap())?;

                    match decl_kind {
                        z3::DeclKind::FPA_EQ => ctx.fp_eq(a, b),
                        z3::DeclKind::FPA_LT => ctx.fp_lt(a, b),
                        z3::DeclKind::FPA_LE => ctx.fp_leq(a, b),
                        z3::DeclKind::FPA_GT => ctx.fp_gt(a, b),
                        z3::DeclKind::FPA_GE => ctx.fp_geq(a, b),
                        _ => unreachable!(),
                    }
                }
                z3::DeclKind::FPA_IS_NAN => {
                    let a = FloatAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    ctx.fp_is_nan(a)
                }
                z3::DeclKind::FPA_IS_INF => {
                    let a = FloatAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    ctx.fp_is_inf(a)
                }

                z3::DeclKind::SEQ_CONTAINS
                | z3::DeclKind::SEQ_PREFIX
                | z3::DeclKind::SEQ_SUFFIX => {
                    let a = StringAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let b = StringAst::from_z3(ctx, ast.nth_child(1).unwrap())?;

                    match decl_kind {
                        z3::DeclKind::SEQ_CONTAINS => ctx.str_contains(a, b),
                        z3::DeclKind::SEQ_PREFIX => ctx.str_prefix_of(a, b),
                        z3::DeclKind::SEQ_SUFFIX => ctx.str_suffix_of(a, b),
                        _ => unreachable!(),
                    }
                }

                z3::DeclKind::ITE => {
                    let cond = BoolAst::from_z3(ctx, ast.nth_child(0).unwrap())?;
                    let then = BoolAst::from_z3(ctx, ast.nth_child(1).unwrap())?;
                    let else_ = BoolAst::from_z3(ctx, ast.nth_child(2).unwrap())?;
                    ctx.ite(cond, then, else_)
                }
                z3::DeclKind::UNINTERPRETED => {
                    // Verify it's a boolean
                    if ast.sort_kind() != z3::SortKind::Bool {
                        return Err(ClarirsError::ConversionError(
                            "expected a boolean".to_string(),
                        ));
                    }
                    let name = decl.name();
                    ctx.bools(&name)
                }
                _ => {
                    let decl_name = format!("{decl}");
                    Err(ClarirsError::ConversionError(format!(
                        "Failed converting from z3: unknown decl kind for bool: {decl_name}"
                    )))
                }
            }
        }
        _ => Err(ClarirsError::ConversionError(
            "Failed converting from z3: unknown ast kind for bool".to_string(),
        )),
    }
}
