use crate::{
    astext::AstExt,
    convert::{convert_bv_to_z3, convert_float_to_z3, convert_string_to_z3},
};
use clarirs_core::prelude::*;
use z3::{ast::Ast, DeclKind};

use super::convert_bv_from_z3;

pub fn convert_bool_to_z3<'z>(
    z3_ctx: &'z z3::Context,
    ast: &BoolAst,
) -> Result<z3::ast::Bool<'z>, ClarirsError> {
    match ast.op() {
        BooleanOp::BoolS(s) => Ok(z3::ast::Bool::new_const(z3_ctx, s.as_str())),
        BooleanOp::BoolV(b) => Ok(z3::ast::Bool::from_bool(z3_ctx, *b)),
        BooleanOp::Not(a) => {
            let a_z3 = convert_bool_to_z3(z3_ctx, a)?;
            Ok(a_z3.not())
        }
        BooleanOp::And(a, b) => {
            let a_z3 = convert_bool_to_z3(z3_ctx, a)?;
            let b_z3 = convert_bool_to_z3(z3_ctx, b)?;
            Ok(z3::ast::Bool::and(z3_ctx, &[&a_z3, &b_z3]))
        }
        BooleanOp::Or(a, b) => {
            let a_z3 = convert_bool_to_z3(z3_ctx, a)?;
            let b_z3 = convert_bool_to_z3(z3_ctx, b)?;
            Ok(z3::ast::Bool::or(z3_ctx, &[&a_z3, &b_z3]))
        }
        BooleanOp::Xor(a, b) => {
            let a_z3 = convert_bool_to_z3(z3_ctx, a)?;
            let b_z3 = convert_bool_to_z3(z3_ctx, b)?;
            Ok(a_z3.xor(&b_z3))
        }
        BooleanOp::BoolEq(a, b) => {
            let a_z3 = convert_bool_to_z3(z3_ctx, a)?;
            let b_z3 = convert_bool_to_z3(z3_ctx, b)?;
            Ok(z3::ast::Bool::_eq(&a_z3, &b_z3))
        }
        BooleanOp::BoolNeq(a, b) => {
            let a_z3 = convert_bool_to_z3(z3_ctx, a)?;
            let b_z3 = convert_bool_to_z3(z3_ctx, b)?;
            Ok(z3::ast::Bool::_eq(&a_z3, &b_z3).not())
        }
        BooleanOp::Eq(a, b) => {
            let a_z3 = convert_bv_to_z3(z3_ctx, a)?;
            let b_z3 = convert_bv_to_z3(z3_ctx, b)?;
            Ok(z3::ast::BV::_eq(&a_z3, &b_z3))
        }
        BooleanOp::Neq(a, b) => {
            let a_z3 = convert_bv_to_z3(z3_ctx, a)?;
            let b_z3 = convert_bv_to_z3(z3_ctx, b)?;
            Ok(z3::ast::BV::_eq(&a_z3, &b_z3).not())
        }
        BooleanOp::ULT(a, b) => {
            let a_z3 = convert_bv_to_z3(z3_ctx, a)?;
            let b_z3 = convert_bv_to_z3(z3_ctx, b)?;
            Ok(a_z3.bvult(&b_z3))
        }
        BooleanOp::ULE(a, b) => {
            let a_z3 = convert_bv_to_z3(z3_ctx, a)?;
            let b_z3 = convert_bv_to_z3(z3_ctx, b)?;
            Ok(a_z3.bvule(&b_z3))
        }
        BooleanOp::UGT(a, b) => {
            let a_z3 = convert_bv_to_z3(z3_ctx, a)?;
            let b_z3 = convert_bv_to_z3(z3_ctx, b)?;
            Ok(a_z3.bvugt(&b_z3))
        }
        BooleanOp::UGE(a, b) => {
            let a_z3 = convert_bv_to_z3(z3_ctx, a)?;
            let b_z3 = convert_bv_to_z3(z3_ctx, b)?;
            Ok(a_z3.bvuge(&b_z3))
        }
        BooleanOp::SLT(a, b) => {
            let a_z3 = convert_bv_to_z3(z3_ctx, a)?;
            let b_z3 = convert_bv_to_z3(z3_ctx, b)?;
            Ok(a_z3.bvslt(&b_z3))
        }
        BooleanOp::SLE(a, b) => {
            let a_z3 = convert_bv_to_z3(z3_ctx, a)?;
            let b_z3 = convert_bv_to_z3(z3_ctx, b)?;
            Ok(a_z3.bvsle(&b_z3))
        }
        BooleanOp::SGT(a, b) => {
            let a_z3 = convert_bv_to_z3(z3_ctx, a)?;
            let b_z3 = convert_bv_to_z3(z3_ctx, b)?;
            Ok(a_z3.bvsgt(&b_z3))
        }
        BooleanOp::SGE(a, b) => {
            let a_z3 = convert_bv_to_z3(z3_ctx, a)?;
            let b_z3 = convert_bv_to_z3(z3_ctx, b)?;
            Ok(a_z3.bvsge(&b_z3))
        }
        BooleanOp::FpEq(a, b) => {
            let a_z3 = convert_float_to_z3(z3_ctx, a)?;
            let b_z3 = convert_float_to_z3(z3_ctx, b)?;
            Ok(z3::ast::Float::_eq(&a_z3, &b_z3))
        }
        BooleanOp::FpNeq(a, b) => {
            let a_z3 = convert_float_to_z3(z3_ctx, a)?;
            let b_z3 = convert_float_to_z3(z3_ctx, b)?;
            Ok(z3::ast::Float::_eq(&a_z3, &b_z3).not())
        }
        BooleanOp::FpLt(a, b) => {
            let a_z3 = convert_float_to_z3(z3_ctx, a)?;
            let b_z3 = convert_float_to_z3(z3_ctx, b)?;
            Ok(a_z3.lt(&b_z3))
        }
        BooleanOp::FpLeq(a, b) => {
            let a_z3 = convert_float_to_z3(z3_ctx, a)?;
            let b_z3 = convert_float_to_z3(z3_ctx, b)?;
            Ok(a_z3.le(&b_z3))
        }
        BooleanOp::FpGt(a, b) => {
            let a_z3 = convert_float_to_z3(z3_ctx, a)?;
            let b_z3 = convert_float_to_z3(z3_ctx, b)?;
            Ok(a_z3.gt(&b_z3))
        }
        BooleanOp::FpGeq(a, b) => {
            let a_z3 = convert_float_to_z3(z3_ctx, a)?;
            let b_z3 = convert_float_to_z3(z3_ctx, b)?;
            Ok(a_z3.ge(&b_z3))
        }
        BooleanOp::FpIsNan(a) => {
            let a_z3 = convert_float_to_z3(z3_ctx, a)?;
            Ok(a_z3.is_nan())
        }
        BooleanOp::FpIsInf(a) => {
            let a_z3 = convert_float_to_z3(z3_ctx, a)?;
            Ok(a_z3.is_infinite())
        }
        BooleanOp::StrContains(a, b) => {
            let a_z3 = convert_string_to_z3(z3_ctx, a)?;
            let b_z3 = convert_string_to_z3(z3_ctx, b)?;
            Ok(a_z3.contains(&b_z3))
        }
        BooleanOp::StrPrefixOf(a, b) => {
            let a_z3 = convert_string_to_z3(z3_ctx, a)?;
            let b_z3 = convert_string_to_z3(z3_ctx, b)?;
            Ok(a_z3.prefix(&b_z3))
        }
        BooleanOp::StrSuffixOf(a, b) => {
            let a_z3 = convert_string_to_z3(z3_ctx, a)?;
            let b_z3 = convert_string_to_z3(z3_ctx, b)?;
            Ok(a_z3.suffix(&b_z3))
        }
        BooleanOp::StrIsDigit(a) => {
            let _a_z3 = convert_string_to_z3(z3_ctx, a)?;
            todo!("Z3 doesn't actually support this operation")
        }
        BooleanOp::StrEq(a, b) => {
            let a_z3 = convert_string_to_z3(z3_ctx, a)?;
            let b_z3 = convert_string_to_z3(z3_ctx, b)?;
            Ok(z3::ast::String::_eq(&a_z3, &b_z3))
        }
        BooleanOp::StrNeq(a, b) => {
            let a_z3 = convert_string_to_z3(z3_ctx, a)?;
            let b_z3 = convert_string_to_z3(z3_ctx, b)?;
            Ok(z3::ast::String::_eq(&a_z3, &b_z3).not())
        }
        BooleanOp::If(cond, then_expr, else_expr) => {
            let cond_z3 = convert_bool_to_z3(z3_ctx, cond)?;
            let then_z3 = convert_bool_to_z3(z3_ctx, then_expr)?;
            let else_z3 = convert_bool_to_z3(z3_ctx, else_expr)?;
            Ok(z3::ast::Bool::ite(&cond_z3, &then_z3, &else_z3))
        }
        BooleanOp::Annotated(inner, _) => {
            // Ignore annotation and convert inner expression
            convert_bool_to_z3(z3_ctx, inner)
        }
    }
}

pub fn convert_bool_from_z3<'c>(
    ctx: &'c Context<'c>,
    ast: &z3::ast::Bool,
) -> Result<BoolAst<'c>, ClarirsError> {
    let decl = ast.decl();
    let kind = decl.kind();

    match kind {
        // This implementation goes in order of the BooleanOp enum
        // BoolS ???
        DeclKind::TRUE => ctx.true_(),
        DeclKind::FALSE => ctx.false_(),
        DeclKind::NOT => {
            let a = convert_bool_from_z3(ctx, &ast.arg_bool(0)?)?;
            ctx.not(&a)
        }
        DeclKind::AND => {
            let a = convert_bool_from_z3(ctx, &ast.arg_bool(0)?)?;
            let b = convert_bool_from_z3(ctx, &ast.arg_bool(1)?)?;
            ctx.and(&a, &b)
        }
        DeclKind::OR => {
            let a = convert_bool_from_z3(ctx, &ast.arg_bool(0)?)?;
            let b = convert_bool_from_z3(ctx, &ast.arg_bool(1)?)?;
            ctx.or(&a, &b)
        }
        DeclKind::XOR => {
            let a = convert_bool_from_z3(ctx, &ast.arg_bool(0)?)?;
            let b = convert_bool_from_z3(ctx, &ast.arg_bool(1)?)?;
            ctx.xor(&a, &b)
        }
        DeclKind::EQ => {
            let a = convert_bool_from_z3(ctx, &ast.arg_bool(0)?)?;
            let b = convert_bool_from_z3(ctx, &ast.arg_bool(1)?)?;
            ctx.eq_(&a, &b)
        }
        DeclKind::DISTINCT => {
            let a = convert_bool_from_z3(ctx, &ast.arg_bool(0)?)?;
            let b = convert_bool_from_z3(ctx, &ast.arg_bool(1)?)?;
            ctx.neq(&a, &b)
        }
        DeclKind::ULT => {
            let a = convert_bv_from_z3(ctx, &ast.arg_bv(0)?)?;
            let b = convert_bv_from_z3(ctx, &ast.arg_bv(1)?)?;
            ctx.ult(&a, &b)
        }
        DeclKind::UGT => {
            let a = convert_bv_from_z3(ctx, &ast.arg_bv(0)?)?;
            let b = convert_bv_from_z3(ctx, &ast.arg_bv(1)?)?;
            ctx.ugt(&a, &b)
        }
        DeclKind::SLT => {
            let a = convert_bv_from_z3(ctx, &ast.arg_bv(0)?)?;
            let b = convert_bv_from_z3(ctx, &ast.arg_bv(1)?)?;
            ctx.slt(&a, &b)
        }
        DeclKind::SGT => {
            let a = convert_bv_from_z3(ctx, &ast.arg_bv(0)?)?;
            let b = convert_bv_from_z3(ctx, &ast.arg_bv(1)?)?;
            ctx.sgt(&a, &b)
        }

        _ => Err(ClarirsError::ConversionError(format!(
            "Unsupported Z3 AST kind: {:?}",
            ast
        ))),
    }
}
