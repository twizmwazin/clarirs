use crate::astext::{DynamicExt, child};
use clarirs_core::prelude::*;
use z3::ast::{Ast, Bool, Dynamic};

use super::AstExtZ3;

fn binop_bv_cmp(
    children: &[Dynamic],
    op: impl Fn(&z3::ast::BV, &z3::ast::BV) -> Bool,
) -> Result<Dynamic, ClarirsError> {
    Ok(Dynamic::from(op(
        &child(children, 0)?.to_bv()?,
        &child(children, 1)?.to_bv()?,
    )))
}

fn binop_float_cmp(
    children: &[Dynamic],
    op: impl Fn(&z3::ast::Float, &z3::ast::Float) -> Bool,
) -> Result<Dynamic, ClarirsError> {
    Ok(Dynamic::from(op(
        &child(children, 0)?.to_float()?,
        &child(children, 1)?.to_float()?,
    )))
}

fn binop_str(
    children: &[Dynamic],
    op: impl Fn(&z3::ast::String, &z3::ast::String) -> Bool,
) -> Result<Dynamic, ClarirsError> {
    Ok(Dynamic::from(op(
        &child(children, 0)?.to_string_ast()?,
        &child(children, 1)?.to_string_ast()?,
    )))
}

fn bool_fold(children: &[Dynamic], op: impl Fn(&[&Bool]) -> Bool) -> Result<Dynamic, ClarirsError> {
    let args: Vec<Bool> = children
        .iter()
        .map(|c| c.to_bool())
        .collect::<Result<_, _>>()?;
    let refs: Vec<&Bool> = args.iter().collect();
    Ok(Dynamic::from(op(&refs)))
}

pub(crate) fn to_z3(ast: &BoolAst, children: &[Dynamic]) -> Result<Dynamic, ClarirsError> {
    Ok(match ast.op() {
        BooleanOp::BoolS(s) => Dynamic::from(Bool::new_const(s.as_str())),
        BooleanOp::BoolV(b) => Dynamic::from(Bool::from_bool(*b)),
        BooleanOp::Not(..) => Dynamic::from(child(children, 0)?.to_bool()?.not()),
        BooleanOp::And(..) => bool_fold(children, |args| Bool::and(args))?,
        BooleanOp::Or(..) => bool_fold(children, |args| Bool::or(args))?,
        BooleanOp::Xor(..) => Dynamic::from(
            child(children, 0)?
                .to_bool()?
                .xor(&child(children, 1)?.to_bool()?),
        ),
        BooleanOp::ITE(..) => {
            let cond = child(children, 0)?.to_bool()?;
            cond.ite(child(children, 1)?, child(children, 2)?)
        }

        // Equality/inequality (works on any sort via Dynamic)
        BooleanOp::Eq(..) | BooleanOp::BoolEq(..) | BooleanOp::StrEq(..) => {
            Dynamic::from(child(children, 0)?.eq(child(children, 1)?))
        }
        BooleanOp::Neq(..)
        | BooleanOp::BoolNeq(..)
        | BooleanOp::StrNeq(..)
        | BooleanOp::FpNeq(..) => Dynamic::from(Dynamic::distinct(&[
            child(children, 0)?,
            child(children, 1)?,
        ])),

        // BV comparisons
        BooleanOp::ULT(..) => binop_bv_cmp(children, |a, b| a.bvult(b))?,
        BooleanOp::ULE(..) => binop_bv_cmp(children, |a, b| a.bvule(b))?,
        BooleanOp::UGT(..) => binop_bv_cmp(children, |a, b| a.bvugt(b))?,
        BooleanOp::UGE(..) => binop_bv_cmp(children, |a, b| a.bvuge(b))?,
        BooleanOp::SLT(..) => binop_bv_cmp(children, |a, b| a.bvslt(b))?,
        BooleanOp::SLE(..) => binop_bv_cmp(children, |a, b| a.bvsle(b))?,
        BooleanOp::SGT(..) => binop_bv_cmp(children, |a, b| a.bvsgt(b))?,
        BooleanOp::SGE(..) => binop_bv_cmp(children, |a, b| a.bvsge(b))?,

        // FP comparisons
        BooleanOp::FpEq(..) => binop_float_cmp(children, |a, b| a.eq_fpa(b))?,
        BooleanOp::FpLt(..) => binop_float_cmp(children, |a, b| a.lt(b))?,
        BooleanOp::FpLeq(..) => binop_float_cmp(children, |a, b| a.le(b))?,
        BooleanOp::FpGt(..) => binop_float_cmp(children, |a, b| a.gt(b))?,
        BooleanOp::FpGeq(..) => binop_float_cmp(children, |a, b| a.ge(b))?,
        BooleanOp::FpIsNan(..) => Dynamic::from(child(children, 0)?.to_float()?.is_nan()),
        BooleanOp::FpIsInf(..) => Dynamic::from(child(children, 0)?.to_float()?.is_infinite()),

        // String comparisons
        BooleanOp::StrContains(..) => binop_str(children, |a, b| a.contains(b))?,
        BooleanOp::StrPrefixOf(..) => binop_str(children, |a, b| a.prefix(b))?,
        BooleanOp::StrSuffixOf(..) => binop_str(children, |a, b| a.suffix(b))?,
        BooleanOp::StrIsDigit(..) => {
            let a = child(children, 0)?.to_string_ast()?;
            let zero = z3::ast::Int::from_i64(0);
            // str.to_int returns -1 for non-digit strings, so >= 0 means all digits
            let is_non_negative = super::string::str_to_int(&a).ge(&zero);
            let is_non_empty = a.length().gt(&zero);
            Dynamic::from(Bool::and(&[&is_non_negative, &is_non_empty]))
        }
    })
}

pub(crate) fn from_z3<'c>(ctx: &'c Context<'c>, ast: Dynamic) -> Result<BoolAst<'c>, ClarirsError> {
    let ast_kind = ast.kind();
    match ast_kind {
        z3::AstKind::App => {
            let decl = ast.get_decl()?;
            let decl_kind = decl.kind();

            match decl_kind {
                z3::DeclKind::TRUE => ctx.true_(),
                z3::DeclKind::FALSE => ctx.false_(),
                z3::DeclKind::NOT => {
                    let inner = BoolAst::from_z3(ctx, ast.nth(0)?)?;

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
                        args.push(BoolAst::from_z3(ctx, ast.nth(i)?)?);
                    }
                    match decl_kind {
                        z3::DeclKind::AND => ctx.and(args),
                        z3::DeclKind::OR => ctx.or(args),
                        _ => unreachable!(),
                    }
                }
                z3::DeclKind::XOR => {
                    let a = BoolAst::from_z3(ctx, ast.nth(0)?)?;
                    let b = BoolAst::from_z3(ctx, ast.nth(1)?)?;
                    ctx.xor(a, b)
                }
                z3::DeclKind::EQ | z3::DeclKind::DISTINCT => {
                    if decl_kind == z3::DeclKind::DISTINCT && ast.num_children() != 2 {
                        return Err(ClarirsError::ConversionError(
                            "Distinct with != 2 args not supported".into(),
                        ));
                    }
                    let arg0 = ast.nth(0)?;
                    let arg1 = ast.nth(1)?;
                    let is_eq = decl_kind == z3::DeclKind::EQ;
                    match arg0.sort_kind() {
                        z3::SortKind::Bool => {
                            let a = BoolAst::from_z3(ctx, arg0)?;
                            let b = BoolAst::from_z3(ctx, arg1)?;
                            if is_eq { ctx.eq_(a, b) } else { ctx.neq(a, b) }
                        }
                        z3::SortKind::BV => {
                            let a = BitVecAst::from_z3(ctx, arg0)?;
                            let b = BitVecAst::from_z3(ctx, arg1)?;
                            if is_eq { ctx.eq_(a, b) } else { ctx.neq(a, b) }
                        }
                        z3::SortKind::FloatingPoint => {
                            let a = FloatAst::from_z3(ctx, arg0)?;
                            let b = FloatAst::from_z3(ctx, arg1)?;
                            if is_eq {
                                ctx.eq_(a, b)
                            } else {
                                ctx.fp_neq(a, b)
                            }
                        }
                        z3::SortKind::Seq => {
                            let a = StringAst::from_z3(ctx, arg0)?;
                            let b = StringAst::from_z3(ctx, arg1)?;
                            if is_eq {
                                ctx.str_eq(a, b)
                            } else {
                                ctx.str_neq(a, b)
                            }
                        }
                        _ => Err(ClarirsError::ConversionError(
                            "EQ/DISTINCT operand has unrecognized sort".into(),
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
                    let a = BitVecAst::from_z3(ctx, ast.nth(0)?)?;
                    let b = BitVecAst::from_z3(ctx, ast.nth(1)?)?;
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
                    let a = FloatAst::from_z3(ctx, ast.nth(0)?)?;
                    let b = FloatAst::from_z3(ctx, ast.nth(1)?)?;
                    match decl_kind {
                        z3::DeclKind::FPA_EQ => ctx.fp_eq(a, b),
                        z3::DeclKind::FPA_LT => ctx.fp_lt(a, b),
                        z3::DeclKind::FPA_LE => ctx.fp_leq(a, b),
                        z3::DeclKind::FPA_GT => ctx.fp_gt(a, b),
                        z3::DeclKind::FPA_GE => ctx.fp_geq(a, b),
                        _ => unreachable!(),
                    }
                }
                z3::DeclKind::FPA_IS_NAN => ctx.fp_is_nan(FloatAst::from_z3(ctx, ast.nth(0)?)?),
                z3::DeclKind::FPA_IS_INF => ctx.fp_is_inf(FloatAst::from_z3(ctx, ast.nth(0)?)?),
                z3::DeclKind::SEQ_CONTAINS
                | z3::DeclKind::SEQ_PREFIX
                | z3::DeclKind::SEQ_SUFFIX => {
                    let a = StringAst::from_z3(ctx, ast.nth(0)?)?;
                    let b = StringAst::from_z3(ctx, ast.nth(1)?)?;
                    match decl_kind {
                        z3::DeclKind::SEQ_CONTAINS => ctx.str_contains(a, b),
                        z3::DeclKind::SEQ_PREFIX => ctx.str_prefix_of(a, b),
                        z3::DeclKind::SEQ_SUFFIX => ctx.str_suffix_of(a, b),
                        _ => unreachable!(),
                    }
                }
                z3::DeclKind::ITE => {
                    let cond = BoolAst::from_z3(ctx, ast.nth(0)?)?;
                    let then = BoolAst::from_z3(ctx, ast.nth(1)?)?;
                    let else_ = BoolAst::from_z3(ctx, ast.nth(2)?)?;
                    ctx.ite(cond, then, else_)
                }
                z3::DeclKind::UNINTERPRETED => {
                    if ast.sort_kind() != z3::SortKind::Bool {
                        return Err(ClarirsError::ConversionError("expected a boolean".into()));
                    }
                    ctx.bools(decl.name())
                }
                _ => Err(ClarirsError::ConversionError(format!(
                    "Failed converting from z3: unknown decl kind for bool: {decl}"
                ))),
            }
        }
        _ => Err(ClarirsError::ConversionError(
            "Failed converting from z3: unknown ast kind for bool".into(),
        )),
    }
}
