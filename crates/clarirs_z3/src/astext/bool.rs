use std::ffi::CStr;

use crate::{Z3_CONTEXT, astext::child, check_z3_error, rc::RcAst};
use clarirs_core::prelude::*;

use super::AstExtZ3;
use z3_sys::*;

pub(crate) fn to_z3(ast: &BoolAst, children: &[RcAst]) -> Result<RcAst, ClarirsError> {
    Z3_CONTEXT.with(|&z3_ctx| unsafe {
        Ok(match ast.op() {
            BooleanOp::BoolS(s) => {
                let s_cstr = std::ffi::CString::new(s.as_str()).unwrap();
                let sym = Z3_mk_string_symbol(z3_ctx, s_cstr.as_ptr())
                    .expect("Z3_mk_string_symbol returned null");
                let sort = Z3_mk_bool_sort(z3_ctx).expect("Z3_mk_bool_sort returned null");
                RcAst::try_from(Z3_mk_const(z3_ctx, sym, sort).expect("Z3_mk_const returned null"))?
            }
            BooleanOp::BoolV(b) => if *b {
                Z3_mk_true(z3_ctx).expect("Z3_mk_true returned null")
            } else {
                Z3_mk_false(z3_ctx).expect("Z3_mk_false returned null")
            }
            .try_into()?,
            BooleanOp::Not(..) => unop!(z3_ctx, children, Z3_mk_not),
            BooleanOp::And(..) => {
                let args: Vec<_> = children.iter().map(|c| **c).collect();
                Z3_mk_and(z3_ctx, args.len() as u32, args.as_ptr())
                    .expect("Z3_mk_and returned null")
                    .try_into()?
            }
            BooleanOp::Or(..) => {
                let args: Vec<_> = children.iter().map(|c| **c).collect();
                Z3_mk_or(z3_ctx, args.len() as u32, args.as_ptr())
                    .expect("Z3_mk_or returned null")
                    .try_into()?
            }
            BooleanOp::Xor(..) => binop!(z3_ctx, children, Z3_mk_xor),
            BooleanOp::BoolEq(..) => binop!(z3_ctx, children, Z3_mk_eq),
            BooleanOp::BoolNeq(..) => {
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                Z3_mk_distinct(z3_ctx, 2, [**a, **b].as_ptr())
                    .expect("Z3_mk_distinct returned null")
                    .try_into()?
            }
            BooleanOp::ITE(..) => {
                let cond = child(children, 0)?;
                let then = child(children, 1)?;
                let else_ = child(children, 2)?;
                Z3_mk_ite(z3_ctx, **cond, **then, **else_)
                    .expect("Z3_mk_ite returned null")
                    .try_into()?
            }

            // BV operations
            BooleanOp::Eq(..) => binop!(z3_ctx, children, Z3_mk_eq),
            BooleanOp::Neq(..) => {
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                Z3_mk_distinct(z3_ctx, 2, [**a, **b].as_ptr())
                    .expect("Z3_mk_distinct returned null")
                    .try_into()?
            }
            BooleanOp::ULT(..) => binop!(z3_ctx, children, Z3_mk_bvult),
            BooleanOp::ULE(..) => binop!(z3_ctx, children, Z3_mk_bvule),
            BooleanOp::UGT(..) => binop!(z3_ctx, children, Z3_mk_bvugt),
            BooleanOp::UGE(..) => binop!(z3_ctx, children, Z3_mk_bvuge),
            BooleanOp::SLT(..) => binop!(z3_ctx, children, Z3_mk_bvslt),
            BooleanOp::SLE(..) => binop!(z3_ctx, children, Z3_mk_bvsle),
            BooleanOp::SGT(..) => binop!(z3_ctx, children, Z3_mk_bvsgt),
            BooleanOp::SGE(..) => binop!(z3_ctx, children, Z3_mk_bvsge),

            // FP operations
            BooleanOp::FpEq(..) => binop!(z3_ctx, children, Z3_mk_fpa_eq),
            BooleanOp::FpNeq(..) => {
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                Z3_mk_distinct(z3_ctx, 2, [**a, **b].as_ptr())
                    .expect("Z3_mk_distinct returned null")
                    .try_into()?
            }
            BooleanOp::FpLt(..) => binop!(z3_ctx, children, Z3_mk_fpa_lt),
            BooleanOp::FpLeq(..) => binop!(z3_ctx, children, Z3_mk_fpa_leq),
            BooleanOp::FpGt(..) => binop!(z3_ctx, children, Z3_mk_fpa_gt),
            BooleanOp::FpGeq(..) => binop!(z3_ctx, children, Z3_mk_fpa_geq),
            BooleanOp::FpIsNan(..) => unop!(z3_ctx, children, Z3_mk_fpa_is_nan),
            BooleanOp::FpIsInf(..) => unop!(z3_ctx, children, Z3_mk_fpa_is_infinite),

            // String operations
            BooleanOp::StrContains(..) => binop!(z3_ctx, children, Z3_mk_seq_contains),
            BooleanOp::StrPrefixOf(..) => binop!(z3_ctx, children, Z3_mk_seq_prefix),
            BooleanOp::StrSuffixOf(..) => binop!(z3_ctx, children, Z3_mk_seq_suffix),
            BooleanOp::StrIsDigit(..) => {
                let a = child(children, 0)?;
                // str.to_int returns -1 for non-digit strings, so >= 0 means all digits
                let int_val =
                    Z3_mk_str_to_int(z3_ctx, **a).expect("Z3_mk_str_to_int returned null");
                let int_sort = Z3_mk_int_sort(z3_ctx).expect("Z3_mk_int_sort returned null");
                let zero_cstr = std::ffi::CString::new("0").unwrap();
                let zero = Z3_mk_numeral(z3_ctx, zero_cstr.as_ptr(), int_sort)
                    .expect("Z3_mk_numeral returned null");
                let is_non_negative =
                    Z3_mk_ge(z3_ctx, int_val, zero).expect("Z3_mk_ge returned null");
                // Also require non-empty string
                let str_len =
                    Z3_mk_seq_length(z3_ctx, **a).expect("Z3_mk_seq_length returned null");
                let zero_int_cstr = std::ffi::CString::new("0").unwrap();
                let zero_int = Z3_mk_numeral(z3_ctx, zero_int_cstr.as_ptr(), int_sort)
                    .expect("Z3_mk_numeral returned null");
                let is_non_empty =
                    Z3_mk_gt(z3_ctx, str_len, zero_int).expect("Z3_mk_gt returned null");
                let args = [is_non_negative, is_non_empty];
                Z3_mk_and(z3_ctx, 2, args.as_ptr())
                    .expect("Z3_mk_and returned null")
                    .try_into()?
            }
            BooleanOp::StrEq(..) => binop!(z3_ctx, children, Z3_mk_eq),
            BooleanOp::StrNeq(..) => {
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                Z3_mk_distinct(z3_ctx, 2, [**a, **b].as_ptr())
                    .expect("Z3_mk_distinct returned null")
                    .try_into()?
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
        let ast_kind = Z3_get_ast_kind(*z3_ctx, *ast);
        match ast_kind {
            AstKind::App => {
                let app = Z3_to_app(*z3_ctx, *ast).expect("Z3_to_app returned null");
                let decl = Z3_get_app_decl(*z3_ctx, app).expect("Z3_get_app_decl returned null");
                let decl_kind = Z3_get_decl_kind(*z3_ctx, decl);

                match decl_kind {
                    DeclKind::TRUE => ctx.true_(),
                    DeclKind::FALSE => ctx.false_(),
                    DeclKind::NOT => {
                        let arg = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let inner = BoolAst::from_z3(ctx, arg)?;

                        // Special case: if the inner expression is a BoolEq, convert to BoolNeq
                        if let BooleanOp::BoolEq(a, b) = inner.op() {
                            ctx.neq(a, b)
                        } else {
                            ctx.not(inner)
                        }
                    }
                    DeclKind::AND | DeclKind::OR => {
                        let num_args = Z3_get_app_num_args(*z3_ctx, app);
                        let mut args = Vec::with_capacity(num_args as usize);
                        for i in 0..num_args {
                            let arg = RcAst::try_from(
                                Z3_get_app_arg(*z3_ctx, app, i)
                                    .expect("Z3_get_app_arg returned null"),
                            )?;
                            args.push(BoolAst::from_z3(ctx, arg)?);
                        }
                        match decl_kind {
                            DeclKind::AND => ctx.and(args),
                            DeclKind::OR => ctx.or(args),
                            _ => unreachable!(),
                        }
                    }
                    DeclKind::XOR => {
                        let arg0 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let arg1 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"),
                        )?;
                        let a = BoolAst::from_z3(ctx, arg0)?;
                        let b = BoolAst::from_z3(ctx, arg1)?;
                        ctx.xor(a, b)
                    }
                    DeclKind::EQ => {
                        let arg0 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let arg1 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"),
                        )?;
                        let sort = Z3_get_sort(*z3_ctx, *arg0).expect("Z3_get_sort returned null");
                        let sort_kind = Z3_get_sort_kind(*z3_ctx, sort);

                        match sort_kind {
                            SortKind::Bool => {
                                let lhs = BoolAst::from_z3(ctx, arg0)?;
                                let rhs = BoolAst::from_z3(ctx, arg1)?;
                                ctx.eq_(lhs, rhs)
                            }
                            SortKind::BV => {
                                let lhs = BitVecAst::from_z3(ctx, arg0)?;
                                let rhs = BitVecAst::from_z3(ctx, arg1)?;
                                ctx.eq_(lhs, rhs)
                            }
                            SortKind::FloatingPoint => {
                                let lhs = FloatAst::from_z3(ctx, arg0)?;
                                let rhs = FloatAst::from_z3(ctx, arg1)?;
                                ctx.eq_(lhs, rhs)
                            }
                            SortKind::Seq => {
                                let lhs = StringAst::from_z3(ctx, arg0)?;
                                let rhs = StringAst::from_z3(ctx, arg1)?;
                                ctx.str_eq(lhs, rhs)
                            }
                            _ => Err(ClarirsError::ConversionError(
                                "Eq operand has unrecognized sort".to_string(),
                            )),
                        }
                    }
                    DeclKind::DISTINCT => {
                        if Z3_get_app_num_args(*z3_ctx, app) != 2 {
                            return Err(ClarirsError::ConversionError(
                                "Distinct with != 2 args not supported".to_string(),
                            ));
                        }
                        let arg0 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let arg1 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"),
                        )?;
                        let sort = Z3_get_sort(*z3_ctx, *arg0).expect("Z3_get_sort returned null");
                        let sort_kind = Z3_get_sort_kind(*z3_ctx, sort);

                        match sort_kind {
                            SortKind::Bool => {
                                let lhs = BoolAst::from_z3(ctx, arg0)?;
                                let rhs = BoolAst::from_z3(ctx, arg1)?;
                                ctx.neq(lhs, rhs)
                            }
                            SortKind::BV => {
                                let lhs = BitVecAst::from_z3(ctx, arg0)?;
                                let rhs = BitVecAst::from_z3(ctx, arg1)?;
                                ctx.neq(lhs, rhs)
                            }
                            SortKind::FloatingPoint => {
                                let lhs = FloatAst::from_z3(ctx, arg0)?;
                                let rhs = FloatAst::from_z3(ctx, arg1)?;
                                ctx.fp_neq(lhs, rhs)
                            }
                            SortKind::Seq => {
                                let lhs = StringAst::from_z3(ctx, arg0)?;
                                let rhs = StringAst::from_z3(ctx, arg1)?;
                                ctx.str_neq(lhs, rhs)
                            }
                            _ => Err(ClarirsError::ConversionError(
                                "Distinct operand has unrecognized sort".to_string(),
                            )),
                        }
                    }
                    DeclKind::ULT
                    | DeclKind::ULEQ
                    | DeclKind::UGT
                    | DeclKind::UGEQ
                    | DeclKind::SLT
                    | DeclKind::SLEQ
                    | DeclKind::SGT
                    | DeclKind::SGEQ => {
                        let arg0 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let arg1 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"),
                        )?;

                        // Convert both arguments
                        let a = BitVecAst::from_z3(ctx, arg0)?;
                        let b = BitVecAst::from_z3(ctx, arg1)?;

                        // Create the appropriate operation
                        match decl_kind {
                            DeclKind::ULT => ctx.ult(a, b),
                            DeclKind::ULEQ => ctx.ule(a, b),
                            DeclKind::UGT => ctx.ugt(a, b),
                            DeclKind::UGEQ => ctx.uge(a, b),
                            DeclKind::SLT => ctx.slt(a, b),
                            DeclKind::SLEQ => ctx.sle(a, b),
                            DeclKind::SGT => ctx.sgt(a, b),
                            DeclKind::SGEQ => ctx.sge(a, b),
                            _ => unreachable!(),
                        }
                    }
                    // FP comparisons
                    DeclKind::FPA_EQ
                    | DeclKind::FPA_LT
                    | DeclKind::FPA_LE
                    | DeclKind::FPA_GT
                    | DeclKind::FPA_GE => {
                        let arg0 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let arg1 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"),
                        )?;

                        let a = FloatAst::from_z3(ctx, arg0)?;
                        let b = FloatAst::from_z3(ctx, arg1)?;

                        match decl_kind {
                            DeclKind::FPA_EQ => ctx.fp_eq(a, b),
                            DeclKind::FPA_LT => ctx.fp_lt(a, b),
                            DeclKind::FPA_LE => ctx.fp_leq(a, b),
                            DeclKind::FPA_GT => ctx.fp_gt(a, b),
                            DeclKind::FPA_GE => ctx.fp_geq(a, b),
                            _ => unreachable!(),
                        }
                    }
                    DeclKind::FPA_IS_NAN => {
                        let arg0 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let a = FloatAst::from_z3(ctx, arg0)?;
                        ctx.fp_is_nan(a)
                    }
                    DeclKind::FPA_IS_INF => {
                        let arg0 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let a = FloatAst::from_z3(ctx, arg0)?;
                        ctx.fp_is_inf(a)
                    }

                    // String predicates
                    DeclKind::SEQ_CONTAINS | DeclKind::SEQ_PREFIX | DeclKind::SEQ_SUFFIX => {
                        let arg0 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let arg1 = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"),
                        )?;

                        let a = StringAst::from_z3(ctx, arg0)?;
                        let b = StringAst::from_z3(ctx, arg1)?;

                        match decl_kind {
                            DeclKind::SEQ_CONTAINS => ctx.str_contains(a, b),
                            DeclKind::SEQ_PREFIX => ctx.str_prefix_of(a, b),
                            DeclKind::SEQ_SUFFIX => ctx.str_suffix_of(a, b),
                            _ => unreachable!(),
                        }
                    }

                    DeclKind::ITE => {
                        let cond = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"),
                        )?;
                        let then = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"),
                        )?;
                        let else_ = RcAst::try_from(
                            Z3_get_app_arg(*z3_ctx, app, 2).expect("Z3_get_app_arg returned null"),
                        )?;
                        let cond = BoolAst::from_z3(ctx, cond)?;
                        let then = BoolAst::from_z3(ctx, then)?;
                        let else_ = BoolAst::from_z3(ctx, else_)?;
                        ctx.ite(cond, then, else_)
                    }
                    DeclKind::UNINTERPRETED => {
                        // Verify it's a boolean
                        let sort = Z3_get_sort(*z3_ctx, *ast).expect("Z3_get_sort returned null");
                        let bool_sort =
                            Z3_mk_bool_sort(*z3_ctx).expect("Z3_mk_bool_sort returned null");
                        if sort != bool_sort {
                            return Err(ClarirsError::ConversionError(
                                "expected a boolean".to_string(),
                            ));
                        }
                        let sym = Z3_get_decl_name(*z3_ctx, decl)
                            .expect("Z3_get_decl_name returned null");
                        let name = Z3_get_symbol_string(*z3_ctx, sym);
                        let name = std::ffi::CStr::from_ptr(name).to_str().unwrap();
                        ctx.bools(name)
                    }
                    _ => {
                        let decl_name =
                            CStr::from_ptr(Z3_func_decl_to_string(*z3_ctx, decl) as *mut i8)
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
