use std::ffi::CStr;

use crate::{Z3_CONTEXT, check_z3_error, rc::RcAst};
use clarirs_core::prelude::*;
use clarirs_z3_sys as z3;

use super::AstExtZ3;

pub(crate) fn to_z3(ast: &BoolAst, children: &[RcAst]) -> Result<RcAst, ClarirsError> {
    Z3_CONTEXT.with(|&z3_ctx| unsafe {
        Ok(match ast.op() {
            BooleanOp::BoolS(s) => {
                let s_cstr = std::ffi::CString::new(s.as_str()).unwrap();
                let sym = z3::mk_string_symbol(z3_ctx, s_cstr.as_ptr());
                let sort = z3::mk_bool_sort(z3_ctx);
                RcAst::try_from(z3::mk_const(z3_ctx, sym, sort))?
            }
            BooleanOp::BoolV(b) => if *b {
                z3::mk_true(z3_ctx)
            } else {
                z3::mk_false(z3_ctx)
            }
            .try_into()?,
            BooleanOp::Not(..) => unop!(z3_ctx, children, mk_not),
            BooleanOp::And(..) => {
                let args = [child!(children, 0).0, child!(children, 1).0];
                z3::mk_and(z3_ctx, 2, args.as_ptr()).try_into()?
            }
            BooleanOp::Or(..) => {
                let args = [child!(children, 0).0, child!(children, 1).0];
                z3::mk_or(z3_ctx, 2, args.as_ptr()).try_into()?
            }
            BooleanOp::Xor(..) => binop!(z3_ctx, children, mk_xor),
            BooleanOp::BoolEq(..) => binop!(z3_ctx, children, mk_eq),
            BooleanOp::BoolNeq(..) => {
                let a = child!(children, 0);
                let b = child!(children, 1);
                z3::mk_distinct(z3_ctx, 2, [a.0, b.0].as_ptr()).try_into()?
            }
            BooleanOp::If(..) => {
                let cond = child!(children, 0);
                let then = child!(children, 1);
                let else_ = child!(children, 2);
                z3::mk_ite(z3_ctx, cond.0, then.0, else_.0).try_into()?
            }

            // BV operations
            BooleanOp::Eq(..) => binop!(z3_ctx, children, mk_eq),
            BooleanOp::Neq(..) => {
                let a = child!(children, 0);
                let b = child!(children, 1);
                z3::mk_distinct(z3_ctx, 2, [a.0, b.0].as_ptr()).try_into()?
            }
            BooleanOp::ULT(..) => binop!(z3_ctx, children, mk_bvult),
            BooleanOp::ULE(..) => binop!(z3_ctx, children, mk_bvule),
            BooleanOp::UGT(..) => binop!(z3_ctx, children, mk_bvugt),
            BooleanOp::UGE(..) => binop!(z3_ctx, children, mk_bvuge),
            BooleanOp::SLT(..) => binop!(z3_ctx, children, mk_bvslt),
            BooleanOp::SLE(..) => binop!(z3_ctx, children, mk_bvsle),
            BooleanOp::SGT(..) => binop!(z3_ctx, children, mk_bvsgt),
            BooleanOp::SGE(..) => binop!(z3_ctx, children, mk_bvsge),

            // FP operations
            BooleanOp::FpEq(..) => binop!(z3_ctx, children, mk_fpa_eq),
            BooleanOp::FpNeq(..) => {
                let a = child!(children, 0);
                let b = child!(children, 1);
                z3::mk_distinct(z3_ctx, 2, [a.0, b.0].as_ptr()).try_into()?
            }
            BooleanOp::FpLt(..) => binop!(z3_ctx, children, mk_fpa_lt),
            BooleanOp::FpLeq(..) => binop!(z3_ctx, children, mk_fpa_leq),
            BooleanOp::FpGt(..) => binop!(z3_ctx, children, mk_fpa_gt),
            BooleanOp::FpGeq(..) => binop!(z3_ctx, children, mk_fpa_geq),
            BooleanOp::FpIsNan(..) => unop!(z3_ctx, children, mk_fpa_is_nan),
            BooleanOp::FpIsInf(..) => unop!(z3_ctx, children, mk_fpa_is_infinite),

            // String operations
            BooleanOp::StrContains(..) => binop!(z3_ctx, children, mk_seq_contains),
            BooleanOp::StrPrefixOf(..) => binop!(z3_ctx, children, mk_seq_prefix),
            BooleanOp::StrSuffixOf(..) => binop!(z3_ctx, children, mk_seq_suffix),
            BooleanOp::StrIsDigit(..) => todo!("StrIsDigit - no direct Z3 equivalent"),
            BooleanOp::StrEq(..) => binop!(z3_ctx, children, mk_eq),
            BooleanOp::StrNeq(..) => {
                let a = child!(children, 0);
                let b = child!(children, 1);
                z3::mk_distinct(z3_ctx, 2, [a.0, b.0].as_ptr()).try_into()?
            }
        })
        .and_then(|maybe_null| {
            check_z3_error()?;
            Ok(maybe_null)
        })
    })
}

pub(crate) fn from_z3<'c>(
    ctx: &'c Context<'c>,
    ast: impl Into<RcAst>,
) -> Result<BoolAst<'c>, ClarirsError> {
    Z3_CONTEXT.with(|z3_ctx| unsafe {
        let ast = ast.into();
        let ast_kind = z3::get_ast_kind(*z3_ctx, *ast);
        match ast_kind {
            z3::AstKind::App => {
                let app = z3::to_app(*z3_ctx, *ast);
                let decl = z3::get_app_decl(*z3_ctx, app);
                let decl_kind = z3::get_decl_kind(*z3_ctx, decl);

                match decl_kind {
                    z3::DeclKind::True => ctx.true_(),
                    z3::DeclKind::False => ctx.false_(),
                    z3::DeclKind::Not => {
                        let arg = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let inner = BoolAst::from_z3(ctx, arg)?;

                        // Special case: if the inner expression is a BoolEq, convert to BoolNeq
                        if let BooleanOp::BoolEq(a, b) = inner.op() {
                            ctx.neq(a, b)
                        } else {
                            ctx.not(inner)
                        }
                    }
                    z3::DeclKind::And | z3::DeclKind::Or | z3::DeclKind::Xor => {
                        let arg0 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let arg1 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 1))?;

                        // Convert both arguments
                        let a = BoolAst::from_z3(ctx, arg0)?;
                        let b = BoolAst::from_z3(ctx, arg1)?;

                        // Create the appropriate operation
                        match decl_kind {
                            z3::DeclKind::And => ctx.and(a, b),
                            z3::DeclKind::Or => ctx.or(a, b),
                            z3::DeclKind::Xor => ctx.xor(a, b),
                            _ => unreachable!(),
                        }
                    }
                    z3::DeclKind::Eq => {
                        let arg0 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let arg1 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 1))?;

                        if let Ok(lhs) = BoolAst::from_z3(ctx, &arg0) {
                            if let Ok(rhs) = BoolAst::from_z3(ctx, arg1) {
                                ctx.eq_(lhs, rhs)
                            } else {
                                Err(ClarirsError::ConversionError(
                                    "Eq lhs is bool, rhs is not".to_string(),
                                ))
                            }
                        } else if let Ok(lhs) = BitVecAst::from_z3(ctx, &arg0) {
                            if let Ok(rhs) = BitVecAst::from_z3(ctx, arg1) {
                                ctx.eq_(lhs, rhs)
                            } else {
                                Err(ClarirsError::ConversionError(
                                    "Eq lhs is bv, rhs is not".to_string(),
                                ))
                            }
                        } else if let Ok(lhs) = FloatAst::from_z3(ctx, &arg0) {
                            if let Ok(rhs) = FloatAst::from_z3(ctx, arg1) {
                                ctx.eq_(lhs, rhs)
                            } else {
                                Err(ClarirsError::ConversionError(
                                    "Eq lhs is fp, rhs is not".to_string(),
                                ))
                            }
                        } else if let Ok(lhs) = StringAst::from_z3(ctx, &arg0) {
                            if let Ok(rhs) = StringAst::from_z3(ctx, arg1) {
                                ctx.eq_(lhs, rhs)
                            } else {
                                Err(ClarirsError::ConversionError(
                                    "Eq lhs is string, rhs is not".to_string(),
                                ))
                            }
                        } else {
                            Err(ClarirsError::ConversionError(
                                "Eq lhs is not a recognized type".to_string(),
                            ))
                        }
                    }
                    z3::DeclKind::Distinct => {
                        // Check args are exactly 2, otherwise error
                        if z3::get_app_num_args(*z3_ctx, app) != 2 {
                            return Err(ClarirsError::ConversionError(
                                "Distinct with != 2 args not supported".to_string(),
                            ));
                        }
                        let arg0 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let arg1 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 1))?;
                        if let Ok(lhs) = BoolAst::from_z3(ctx, &arg0) {
                            if let Ok(rhs) = BoolAst::from_z3(ctx, arg1) {
                                ctx.neq(lhs, rhs)
                            } else {
                                Err(ClarirsError::ConversionError(
                                    "Neq lhs is bool, rhs is not".to_string(),
                                ))
                            }
                        } else if let Ok(lhs) = BitVecAst::from_z3(ctx, &arg0) {
                            if let Ok(rhs) = BitVecAst::from_z3(ctx, arg1) {
                                ctx.neq(lhs, rhs)
                            } else {
                                Err(ClarirsError::ConversionError(
                                    "Neq lhs is bv, rhs is not".to_string(),
                                ))
                            }
                        } else if let Ok(lhs) = FloatAst::from_z3(ctx, &arg0) {
                            if let Ok(rhs) = FloatAst::from_z3(ctx, arg1) {
                                ctx.neq(lhs, rhs)
                            } else {
                                Err(ClarirsError::ConversionError(
                                    "Neq lhs is fp, rhs is not".to_string(),
                                ))
                            }
                        } else if let Ok(lhs) = StringAst::from_z3(ctx, &arg0) {
                            if let Ok(rhs) = StringAst::from_z3(ctx, arg1) {
                                ctx.neq(lhs, rhs)
                            } else {
                                Err(ClarirsError::ConversionError(
                                    "Neq lhs is string, rhs is not".to_string(),
                                ))
                            }
                        } else {
                            Err(ClarirsError::ConversionError(
                                "Neq lhs is not a recognized type".to_string(),
                            ))
                        }
                    }
                    z3::DeclKind::Ult
                    | z3::DeclKind::Uleq
                    | z3::DeclKind::Ugt
                    | z3::DeclKind::Ugeq
                    | z3::DeclKind::Slt
                    | z3::DeclKind::Sleq
                    | z3::DeclKind::Sgt
                    | z3::DeclKind::Sgeq => {
                        let arg0 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let arg1 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 1))?;

                        // Convert both arguments
                        let a = BitVecAst::from_z3(ctx, arg0)?;
                        let b = BitVecAst::from_z3(ctx, arg1)?;

                        // Create the appropriate operation
                        match decl_kind {
                            z3::DeclKind::Ult => ctx.ult(a, b),
                            z3::DeclKind::Uleq => ctx.ule(a, b),
                            z3::DeclKind::Ugt => ctx.ugt(a, b),
                            z3::DeclKind::Ugeq => ctx.uge(a, b),
                            z3::DeclKind::Slt => ctx.slt(a, b),
                            z3::DeclKind::Sleq => ctx.sle(a, b),
                            z3::DeclKind::Sgt => ctx.sgt(a, b),
                            z3::DeclKind::Sgeq => ctx.sge(a, b),
                            _ => unreachable!(),
                        }
                    }
                    z3::DeclKind::Ite => {
                        let cond = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let then = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 1))?;
                        let else_ = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 2))?;
                        let cond = BoolAst::from_z3(ctx, cond)?;
                        let then = BoolAst::from_z3(ctx, then)?;
                        let else_ = BoolAst::from_z3(ctx, else_)?;
                        ctx.if_(cond, then, else_)
                    }
                    z3::DeclKind::Uninterpreted => {
                        // Verify it's a boolean
                        let sort = z3::get_sort(*z3_ctx, *ast);
                        let bool_sort = z3::mk_bool_sort(*z3_ctx);
                        if sort != bool_sort {
                            return Err(ClarirsError::ConversionError(
                                "expected a boolean".to_string(),
                            ));
                        }
                        let sym = z3::get_decl_name(*z3_ctx, decl);
                        let name = z3::get_symbol_string(*z3_ctx, sym);
                        let name = std::ffi::CStr::from_ptr(name).to_str().unwrap();
                        ctx.bools(name)
                    }
                    _ => {
                        let decl_name =
                            CStr::from_ptr(z3::func_decl_to_string(*z3_ctx, decl) as *mut i8)
                                .to_string_lossy();

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
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    // Helper functions to verify Z3 AST structure and values
    fn verify_z3_ast_kind(ast: z3::Ast, expected_kind: z3::DeclKind) -> bool {
        Z3_CONTEXT.with(|z3_ctx| unsafe {
            let app = z3::to_app(*z3_ctx, ast);
            let decl = z3::get_app_decl(*z3_ctx, app);
            let kind = z3::get_decl_kind(*z3_ctx, decl);
            kind == expected_kind
        })
    }

    fn verify_z3_bool_value(ast: z3::Ast, expected_value: bool) -> bool {
        Z3_CONTEXT.with(|z3_ctx| unsafe {
            let app = z3::to_app(*z3_ctx, ast);
            let decl = z3::get_app_decl(*z3_ctx, app);
            let kind = z3::get_decl_kind(*z3_ctx, decl);
            matches!(
                (kind, expected_value),
                (z3::DeclKind::True, true) | (z3::DeclKind::False, false)
            )
        })
    }

    fn verify_z3_symbol_name(ast: z3::Ast, expected_name: &str) -> bool {
        Z3_CONTEXT.with(|z3_ctx| unsafe {
            // For non-constant ASTs, we need to handle the case where the AST is an application
            let ast_kind = z3::get_ast_kind(*z3_ctx, ast);
            if ast_kind != z3::AstKind::App {
                return false;
            }

            let app = z3::to_app(*z3_ctx, ast);
            let decl = z3::get_app_decl(*z3_ctx, app);
            let decl_kind = z3::get_decl_kind(*z3_ctx, decl);

            // Only proceed if this is an uninterpreted function (symbol)
            if decl_kind != z3::DeclKind::Uninterpreted {
                return false;
            }

            let sym = z3::get_decl_name(*z3_ctx, decl);
            let name = z3::get_symbol_string(*z3_ctx, sym);
            let name = std::ffi::CStr::from_ptr(name).to_str().unwrap();
            name == expected_name
        })
    }

    fn get_z3_app_arg(ast: z3::Ast, index: u32) -> Option<z3::Ast> {
        Z3_CONTEXT.with(|z3_ctx| unsafe {
            let ast_kind = z3::get_ast_kind(*z3_ctx, ast);
            if ast_kind != z3::AstKind::App {
                return None;
            }

            let app = z3::to_app(*z3_ctx, ast);
            let num_args = z3::get_app_num_args(*z3_ctx, app);
            if index >= num_args {
                return None;
            }

            Some(z3::get_app_arg(*z3_ctx, app, index))
        })
    }

    fn round_trip<'c>(
        ctx: &'c Context<'c>,
        ast: &BoolAst<'c>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        BoolAst::from_z3(ctx, ast.to_z3()?)
    }

    // One-way conversion tests
    mod to_z3 {
        use super::*;

        #[test]
        fn symbol() {
            let ctx = Context::new();
            let sym = ctx.bools("x").unwrap();

            let z3_ast = sym.to_z3().unwrap();
            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Uninterpreted));
            assert!(verify_z3_symbol_name(*z3_ast, "x"));
        }

        #[test]
        fn values() {
            let ctx = Context::new();
            let t = ctx.true_().unwrap();
            let f = ctx.false_().unwrap();

            let t_z3 = t.to_z3().unwrap();
            let f_z3 = f.to_z3().unwrap();

            assert!(verify_z3_bool_value(*t_z3, true));
            assert!(verify_z3_bool_value(*f_z3, false));
        }

        #[test]
        fn not() {
            let ctx = Context::new();
            let x = ctx.bools("x").unwrap();
            let not_x = ctx.not(x).unwrap();

            let z3_ast = not_x.to_z3().unwrap();
            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Not));

            // Verify the operand is the symbol "x"
            let arg = get_z3_app_arg(*z3_ast, 0).expect("Failed to get NOT argument");
            assert!(
                verify_z3_symbol_name(arg, "x"),
                "NOT argument should be 'x'"
            );
        }

        #[test]
        fn and() {
            let ctx = Context::new();
            let x = ctx.bools("x").unwrap();
            let y = ctx.bools("y").unwrap();
            let and = ctx.and(x, y).unwrap();

            let z3_ast = and.to_z3().unwrap();
            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::And));

            // Verify operands
            let arg0 = get_z3_app_arg(*z3_ast, 0).expect("Failed to get first AND argument");
            let arg1 = get_z3_app_arg(*z3_ast, 1).expect("Failed to get second AND argument");
            assert!(
                verify_z3_symbol_name(arg0, "x"),
                "First AND argument should be 'x'"
            );
            assert!(
                verify_z3_symbol_name(arg1, "y"),
                "Second AND argument should be 'y'"
            );
        }

        #[test]
        fn or() {
            let ctx = Context::new();
            let x = ctx.bools("x").unwrap();
            let y = ctx.bools("y").unwrap();
            let or = ctx.or(x, y).unwrap();

            let z3_ast = or.to_z3().unwrap();
            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Or));

            // Verify operands
            let arg0 = get_z3_app_arg(*z3_ast, 0).expect("Failed to get first OR argument");
            let arg1 = get_z3_app_arg(*z3_ast, 1).expect("Failed to get second OR argument");
            assert!(
                verify_z3_symbol_name(arg0, "x"),
                "First OR argument should be 'x'"
            );
            assert!(
                verify_z3_symbol_name(arg1, "y"),
                "Second OR argument should be 'y'"
            );
        }

        #[test]
        fn xor() {
            let ctx = Context::new();
            let x = ctx.bools("x").unwrap();
            let y = ctx.bools("y").unwrap();
            let xor = ctx.xor(x, y).unwrap();

            let z3_ast = xor.to_z3().unwrap();
            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Xor));

            // Verify operands
            let arg0 = get_z3_app_arg(*z3_ast, 0).expect("Failed to get first XOR argument");
            let arg1 = get_z3_app_arg(*z3_ast, 1).expect("Failed to get second XOR argument");
            assert!(
                verify_z3_symbol_name(arg0, "x"),
                "First XOR argument should be 'x'"
            );
            assert!(
                verify_z3_symbol_name(arg1, "y"),
                "Second XOR argument should be 'y'"
            );
        }

        #[test]
        fn eq() {
            let ctx = Context::new();
            let x = ctx.bools("x").unwrap();
            let y = ctx.bools("y").unwrap();
            let eq = ctx.eq_(x, y).unwrap();

            let z3_ast = eq.to_z3().unwrap();
            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Eq));

            // Verify operands
            let arg0 = get_z3_app_arg(*z3_ast, 0).expect("Failed to get first EQ argument");
            let arg1 = get_z3_app_arg(*z3_ast, 1).expect("Failed to get second EQ argument");
            assert!(
                verify_z3_symbol_name(arg0, "x"),
                "First EQ argument should be 'x'"
            );
            assert!(
                verify_z3_symbol_name(arg1, "y"),
                "Second EQ argument should be 'y'"
            );
        }

        #[test]
        fn neq() {
            let ctx = Context::new();
            let x = ctx.bools("x").unwrap();
            let y = ctx.bools("y").unwrap();
            let neq = ctx.neq(x, y).unwrap();

            let z3_ast = neq.to_z3().unwrap();
            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Distinct));

            // Verify the inner EQ and its operands
            let arg0 = get_z3_app_arg(*z3_ast, 0).expect("Failed to get first NEQ argument");
            let arg1 = get_z3_app_arg(*z3_ast, 1).expect("Failed to get second NEQ argument");
            assert!(
                verify_z3_symbol_name(arg0, "x"),
                "First NEQ argument should be 'x'"
            );
            assert!(
                verify_z3_symbol_name(arg1, "y"),
                "Second NEQ argument should be 'y'"
            );
        }

        #[test]
        fn if_() {
            let ctx = Context::new();
            let cond = ctx.bools("c").unwrap();
            let then = ctx.true_().unwrap();
            let else_ = ctx.false_().unwrap();
            let if_expr = ctx.if_(cond, then, else_).unwrap();

            let z3_ast = if_expr.to_z3().unwrap();
            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Ite));

            // Verify condition and branches
            let cond_ast = get_z3_app_arg(*z3_ast, 0).expect("Failed to get IF condition");
            let then_ast = get_z3_app_arg(*z3_ast, 1).expect("Failed to get IF then branch");
            let else_ast = get_z3_app_arg(*z3_ast, 2).expect("Failed to get IF else branch");

            assert!(
                verify_z3_symbol_name(cond_ast, "c"),
                "IF condition should be 'c'"
            );
            assert!(
                verify_z3_bool_value(then_ast, true),
                "IF then branch should be true"
            );
            assert!(
                verify_z3_bool_value(else_ast, false),
                "IF else branch should be false"
            );
        }
    }

    // Tests for convert_bool_from_z3
    mod from_z3 {
        use super::*;

        #[test]
        fn symbol() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    // Create a Z3 boolean symbol
                    let s_cstr = std::ffi::CString::new("x").unwrap();
                    let sym = z3::mk_string_symbol(*z3_ctx, s_cstr.as_ptr());
                    let sort = z3::mk_bool_sort(*z3_ctx);
                    let decl = z3::mk_func_decl(*z3_ctx, sym, 0, std::ptr::null(), sort);
                    let z3_ast =
                        RcAst::try_from(z3::mk_app(*z3_ctx, decl, 0, std::ptr::null())).unwrap();

                    // Convert from Z3 to Clarirs
                    let result = BoolAst::from_z3(&ctx, z3_ast).unwrap();
                    let expected = ctx.bools("x").unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn values() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let true_z3 = RcAst::try_from(z3::mk_true(*z3_ctx)).unwrap();
                    let false_z3 = RcAst::try_from(z3::mk_false(*z3_ctx)).unwrap();

                    let true_result = BoolAst::from_z3(&ctx, true_z3).unwrap();
                    let false_result = BoolAst::from_z3(&ctx, false_z3).unwrap();

                    assert_eq!(true_result, ctx.true_().unwrap());
                    assert_eq!(false_result, ctx.false_().unwrap());
                });
            }
        }

        #[test]
        fn not() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let x_z3 = {
                        let s_cstr = std::ffi::CString::new("x").unwrap();
                        let sym = z3::mk_string_symbol(*z3_ctx, s_cstr.as_ptr());
                        let sort = z3::mk_bool_sort(*z3_ctx);
                        let decl = z3::mk_func_decl(*z3_ctx, sym, 0, std::ptr::null(), sort);
                        RcAst::try_from(z3::mk_app(*z3_ctx, decl, 0, std::ptr::null())).unwrap()
                    };
                    let not_z3 = RcAst::try_from(z3::mk_not(*z3_ctx, *x_z3)).unwrap();

                    let result = BoolAst::from_z3(&ctx, &not_z3).unwrap();
                    let expected = ctx.not(ctx.bools("x").unwrap()).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn and() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let x_z3 = {
                        let s_cstr = std::ffi::CString::new("x").unwrap();
                        let sym = z3::mk_string_symbol(*z3_ctx, s_cstr.as_ptr());
                        let sort = z3::mk_bool_sort(*z3_ctx);
                        let decl = z3::mk_func_decl(*z3_ctx, sym, 0, std::ptr::null(), sort);
                        RcAst::try_from(z3::mk_app(*z3_ctx, decl, 0, std::ptr::null())).unwrap()
                    };
                    let y_z3 = {
                        let s_cstr = std::ffi::CString::new("y").unwrap();
                        let sym = z3::mk_string_symbol(*z3_ctx, s_cstr.as_ptr());
                        let sort = z3::mk_bool_sort(*z3_ctx);
                        let decl = z3::mk_func_decl(*z3_ctx, sym, 0, std::ptr::null(), sort);
                        RcAst::try_from(z3::mk_app(*z3_ctx, decl, 0, std::ptr::null())).unwrap()
                    };
                    let args = [*x_z3, *y_z3];
                    let and_z3 = RcAst::try_from(z3::mk_and(*z3_ctx, 2, args.as_ptr())).unwrap();

                    let result = BoolAst::from_z3(&ctx, and_z3).unwrap();
                    let expected = ctx
                        .and(ctx.bools("x").unwrap(), ctx.bools("y").unwrap())
                        .unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn or() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let x_z3 = {
                        let s_cstr = std::ffi::CString::new("x").unwrap();
                        let sym = z3::mk_string_symbol(*z3_ctx, s_cstr.as_ptr());
                        let sort = z3::mk_bool_sort(*z3_ctx);
                        let decl = z3::mk_func_decl(*z3_ctx, sym, 0, std::ptr::null(), sort);
                        RcAst::try_from(z3::mk_app(*z3_ctx, decl, 0, std::ptr::null())).unwrap()
                    };
                    let y_z3 = {
                        let s_cstr = std::ffi::CString::new("y").unwrap();
                        let sym = z3::mk_string_symbol(*z3_ctx, s_cstr.as_ptr());
                        let sort = z3::mk_bool_sort(*z3_ctx);
                        let decl = z3::mk_func_decl(*z3_ctx, sym, 0, std::ptr::null(), sort);
                        RcAst::try_from(z3::mk_app(*z3_ctx, decl, 0, std::ptr::null())).unwrap()
                    };
                    let args = [*x_z3, *y_z3];
                    let or_z3 = RcAst::try_from(z3::mk_or(*z3_ctx, 2, args.as_ptr())).unwrap();

                    let result = BoolAst::from_z3(&ctx, or_z3).unwrap();
                    let expected = ctx
                        .or(ctx.bools("x").unwrap(), ctx.bools("y").unwrap())
                        .unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn xor() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let x_z3 = {
                        let s_cstr = std::ffi::CString::new("x").unwrap();
                        let sym = z3::mk_string_symbol(*z3_ctx, s_cstr.as_ptr());
                        let sort = z3::mk_bool_sort(*z3_ctx);
                        let decl = z3::mk_func_decl(*z3_ctx, sym, 0, std::ptr::null(), sort);
                        RcAst::try_from(z3::mk_app(*z3_ctx, decl, 0, std::ptr::null())).unwrap()
                    };
                    let y_z3 = {
                        let s_cstr = std::ffi::CString::new("y").unwrap();
                        let sym = z3::mk_string_symbol(*z3_ctx, s_cstr.as_ptr());
                        let sort = z3::mk_bool_sort(*z3_ctx);
                        let decl = z3::mk_func_decl(*z3_ctx, sym, 0, std::ptr::null(), sort);
                        RcAst::try_from(z3::mk_app(*z3_ctx, decl, 0, std::ptr::null())).unwrap()
                    };
                    let xor_z3 = RcAst::try_from(z3::mk_xor(*z3_ctx, *x_z3, *y_z3)).unwrap();

                    let result = BoolAst::from_z3(&ctx, xor_z3).unwrap();
                    let expected = ctx
                        .xor(ctx.bools("x").unwrap(), ctx.bools("y").unwrap())
                        .unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn eq() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let x_z3 = {
                        let s_cstr = std::ffi::CString::new("x").unwrap();
                        let sym = z3::mk_string_symbol(*z3_ctx, s_cstr.as_ptr());
                        let sort = z3::mk_bool_sort(*z3_ctx);
                        let decl = z3::mk_func_decl(*z3_ctx, sym, 0, std::ptr::null(), sort);
                        RcAst::try_from(z3::mk_app(*z3_ctx, decl, 0, std::ptr::null())).unwrap()
                    };
                    let y_z3 = {
                        let s_cstr = std::ffi::CString::new("y").unwrap();
                        let sym = z3::mk_string_symbol(*z3_ctx, s_cstr.as_ptr());
                        let sort = z3::mk_bool_sort(*z3_ctx);
                        let decl = z3::mk_func_decl(*z3_ctx, sym, 0, std::ptr::null(), sort);
                        RcAst::try_from(z3::mk_app(*z3_ctx, decl, 0, std::ptr::null())).unwrap()
                    };
                    let eq_z3 = RcAst::try_from(z3::mk_eq(*z3_ctx, *x_z3, *y_z3)).unwrap();

                    let result = BoolAst::from_z3(&ctx, eq_z3).unwrap();
                    let expected = ctx
                        .eq_(ctx.bools("x").unwrap(), ctx.bools("y").unwrap())
                        .unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn if_() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let c_z3 = {
                        let s_cstr = std::ffi::CString::new("c").unwrap();
                        let sym = z3::mk_string_symbol(*z3_ctx, s_cstr.as_ptr());
                        let sort = z3::mk_bool_sort(*z3_ctx);
                        let decl = z3::mk_func_decl(*z3_ctx, sym, 0, std::ptr::null(), sort);
                        z3::mk_app(*z3_ctx, decl, 0, std::ptr::null())
                    };
                    let true_z3 = RcAst::try_from(z3::mk_true(*z3_ctx)).unwrap();
                    let false_z3 = RcAst::try_from(z3::mk_false(*z3_ctx)).unwrap();
                    let if_z3 =
                        RcAst::try_from(z3::mk_ite(*z3_ctx, c_z3, true_z3.0, false_z3.0)).unwrap();

                    let result = BoolAst::from_z3(&ctx, if_z3).unwrap();
                    let expected = ctx
                        .if_(
                            ctx.bools("c").unwrap(),
                            ctx.true_().unwrap(),
                            ctx.false_().unwrap(),
                        )
                        .unwrap();
                    assert_eq!(result, expected);
                });
            }
        }
    }
    mod roundtrip {
        use super::*;

        // Round-trip conversion tests
        #[test]
        fn symbol() {
            let ctx = Context::new();
            let sym = ctx.bools("x").unwrap();
            let result = round_trip(&ctx, &sym).unwrap();
            assert_eq!(sym, result);
        }

        #[test]
        fn values() {
            let ctx = Context::new();
            let t = ctx.true_().unwrap();
            let f = ctx.false_().unwrap();

            let t_result = round_trip(&ctx, &t).unwrap();
            let f_result = round_trip(&ctx, &f).unwrap();

            assert_eq!(t, t_result);
            assert_eq!(f, f_result);
        }

        #[test]
        fn not() {
            let ctx = Context::new();
            let x = ctx.bools("x").unwrap();
            let not_x = ctx.not(x).unwrap();

            let result = round_trip(&ctx, &not_x).unwrap();
            assert_eq!(not_x, result);
        }

        #[test]
        fn and() {
            let ctx = Context::new();
            let x = ctx.bools("x").unwrap();
            let y = ctx.bools("y").unwrap();
            let and = ctx.and(x, y).unwrap();

            let result = round_trip(&ctx, &and).unwrap();
            assert_eq!(and, result);
        }

        #[test]
        fn or() {
            let ctx = Context::new();
            let x = ctx.bools("x").unwrap();
            let y = ctx.bools("y").unwrap();
            let or = ctx.or(x, y).unwrap();

            let result = round_trip(&ctx, &or).unwrap();
            assert_eq!(or, result);
        }

        #[test]
        fn xor() {
            let ctx = Context::new();
            let x = ctx.bools("x").unwrap();
            let y = ctx.bools("y").unwrap();
            let xor = ctx.xor(x, y).unwrap();

            let result = round_trip(&ctx, &xor).unwrap();
            assert_eq!(xor, result);
        }

        #[test]
        fn eq() {
            let ctx = Context::new();
            let x = ctx.bools("x").unwrap();
            let y = ctx.bools("y").unwrap();
            let eq = ctx.eq_(x, y).unwrap();

            let result = round_trip(&ctx, &eq).unwrap();
            assert_eq!(eq, result);
        }

        #[test]
        fn neq() {
            let ctx = Context::new();
            let x = ctx.bools("x").unwrap();
            let y = ctx.bools("y").unwrap();
            let neq = ctx.neq(x, y).unwrap();

            let result = round_trip(&ctx, &neq).unwrap();
            assert_eq!(neq, result);
        }

        #[test]
        fn if_() {
            let ctx = Context::new();
            let cond = ctx.bools("c").unwrap();
            let then = ctx.true_().unwrap();
            let else_ = ctx.false_().unwrap();
            let if_expr = ctx.if_(cond, then, else_).unwrap();

            let result = round_trip(&ctx, &if_expr).unwrap();
            assert_eq!(if_expr, result);
        }
    }
}
