use std::ffi::CStr;

use crate::{Z3_CONTEXT, astext::child, check_z3_error, rc::RcAst};
use clarirs_core::prelude::*;

use super::AstExtZ3;

pub(crate) fn to_z3(ast: &BoolAst, children: &[RcAst]) -> Result<RcAst, ClarirsError> {
    Z3_CONTEXT.with(|&z3_ctx| unsafe {
        Ok(match ast.op() {
            BooleanOp::BoolS(s) => {
                let s_cstr = std::ffi::CString::new(s.as_str()).unwrap();
                let sym = z3_sys::Z3_mk_string_symbol(z3_ctx, s_cstr.as_ptr()).expect("Z3_mk_string_symbol returned null");
                let sort = z3_sys::Z3_mk_bool_sort(z3_ctx).expect("Z3_mk_bool_sort returned null");
                RcAst::try_from(z3_sys::Z3_mk_const(z3_ctx, sym, sort).expect("Z3_mk_const returned null"))?
            }
            BooleanOp::BoolV(b) => if *b {
                z3_sys::Z3_mk_true(z3_ctx).expect("Z3_mk_true returned null")
            } else {
                z3_sys::Z3_mk_false(z3_ctx).expect("Z3_mk_false returned null")
            }
            .try_into()?,
            BooleanOp::Not(..) => unop!(z3_ctx, children, Z3_mk_not),
            BooleanOp::And(..) => {
                let args: Vec<_> = children.iter().map(|c| **c).collect();
                z3_sys::Z3_mk_and(z3_ctx, args.len() as u32, args.as_ptr()).expect("Z3_mk_and returned null").try_into()?
            }
            BooleanOp::Or(..) => {
                let args: Vec<_> = children.iter().map(|c| **c).collect();
                z3_sys::Z3_mk_or(z3_ctx, args.len() as u32, args.as_ptr()).expect("Z3_mk_or returned null").try_into()?
            }
            BooleanOp::Xor(..) => binop!(z3_ctx, children, Z3_mk_xor),
            BooleanOp::BoolEq(..) => binop!(z3_ctx, children, Z3_mk_eq),
            BooleanOp::BoolNeq(..) => {
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                z3_sys::Z3_mk_distinct(z3_ctx, 2, [**a, **b].as_ptr()).expect("Z3_mk_distinct returned null").try_into()?
            }
            BooleanOp::ITE(..) => {
                let cond = child(children, 0)?;
                let then = child(children, 1)?;
                let else_ = child(children, 2)?;
                z3_sys::Z3_mk_ite(z3_ctx, **cond, **then, **else_).expect("Z3_mk_ite returned null").try_into()?
            }

            // BV operations
            BooleanOp::Eq(..) => binop!(z3_ctx, children, Z3_mk_eq),
            BooleanOp::Neq(..) => {
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                z3_sys::Z3_mk_distinct(z3_ctx, 2, [**a, **b].as_ptr()).expect("Z3_mk_distinct returned null").try_into()?
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
                z3_sys::Z3_mk_distinct(z3_ctx, 2, [**a, **b].as_ptr()).expect("Z3_mk_distinct returned null").try_into()?
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
                let int_val = z3_sys::Z3_mk_str_to_int(z3_ctx, **a).expect("Z3_mk_str_to_int returned null");
                let int_sort = z3_sys::Z3_mk_int_sort(z3_ctx).expect("Z3_mk_int_sort returned null");
                let zero_cstr = std::ffi::CString::new("0").unwrap();
                let zero = z3_sys::Z3_mk_numeral(z3_ctx, zero_cstr.as_ptr(), int_sort).expect("Z3_mk_numeral returned null");
                let is_non_negative = z3_sys::Z3_mk_ge(z3_ctx, int_val, zero).expect("Z3_mk_ge returned null");
                // Also require non-empty string
                let str_len = z3_sys::Z3_mk_seq_length(z3_ctx, **a).expect("Z3_mk_seq_length returned null");
                let zero_int_cstr = std::ffi::CString::new("0").unwrap();
                let zero_int = z3_sys::Z3_mk_numeral(z3_ctx, zero_int_cstr.as_ptr(), int_sort).expect("Z3_mk_numeral returned null");
                let is_non_empty = z3_sys::Z3_mk_gt(z3_ctx, str_len, zero_int).expect("Z3_mk_gt returned null");
                let args = [is_non_negative, is_non_empty];
                z3_sys::Z3_mk_and(z3_ctx, 2, args.as_ptr()).expect("Z3_mk_and returned null").try_into()?
            }
            BooleanOp::StrEq(..) => binop!(z3_ctx, children, Z3_mk_eq),
            BooleanOp::StrNeq(..) => {
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                z3_sys::Z3_mk_distinct(z3_ctx, 2, [**a, **b].as_ptr()).expect("Z3_mk_distinct returned null").try_into()?
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
        let ast_kind = z3_sys::Z3_get_ast_kind(*z3_ctx, *ast);
        match ast_kind {
            z3_sys::AstKind::App => {
                let app = z3_sys::Z3_to_app(*z3_ctx, *ast).expect("Z3_to_app returned null");
                let decl = z3_sys::Z3_get_app_decl(*z3_ctx, app).expect("Z3_get_app_decl returned null");
                let decl_kind = z3_sys::Z3_get_decl_kind(*z3_ctx, decl);

                match decl_kind {
                    z3_sys::DeclKind::TRUE => ctx.true_(),
                    z3_sys::DeclKind::FALSE => ctx.false_(),
                    z3_sys::DeclKind::NOT => {
                        let arg = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let inner = BoolAst::from_z3(ctx, arg)?;

                        // Special case: if the inner expression is a BoolEq, convert to BoolNeq
                        if let BooleanOp::BoolEq(a, b) = inner.op() {
                            ctx.neq(a, b)
                        } else {
                            ctx.not(inner)
                        }
                    }
                    z3_sys::DeclKind::AND | z3_sys::DeclKind::OR => {
                        let num_args = z3_sys::Z3_get_app_num_args(*z3_ctx, app);
                        let mut args = Vec::with_capacity(num_args as usize);
                        for i in 0..num_args {
                            let arg = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, i).expect("Z3_get_app_arg returned null"))?;
                            args.push(BoolAst::from_z3(ctx, arg)?);
                        }
                        match decl_kind {
                            z3_sys::DeclKind::AND => ctx.and(args),
                            z3_sys::DeclKind::OR => ctx.or(args),
                            _ => unreachable!(),
                        }
                    }
                    z3_sys::DeclKind::XOR => {
                        let arg0 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let arg1 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"))?;
                        let a = BoolAst::from_z3(ctx, arg0)?;
                        let b = BoolAst::from_z3(ctx, arg1)?;
                        ctx.xor(a, b)
                    }
                    z3_sys::DeclKind::EQ => {
                        let arg0 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let arg1 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"))?;
                        let sort = z3_sys::Z3_get_sort(*z3_ctx, *arg0).expect("Z3_get_sort returned null");
                        let sort_kind = z3_sys::Z3_get_sort_kind(*z3_ctx, sort);

                        match sort_kind {
                            z3_sys::SortKind::Bool => {
                                let lhs = BoolAst::from_z3(ctx, arg0)?;
                                let rhs = BoolAst::from_z3(ctx, arg1)?;
                                ctx.eq_(lhs, rhs)
                            }
                            z3_sys::SortKind::BV => {
                                let lhs = BitVecAst::from_z3(ctx, arg0)?;
                                let rhs = BitVecAst::from_z3(ctx, arg1)?;
                                ctx.eq_(lhs, rhs)
                            }
                            z3_sys::SortKind::FloatingPoint => {
                                let lhs = FloatAst::from_z3(ctx, arg0)?;
                                let rhs = FloatAst::from_z3(ctx, arg1)?;
                                ctx.eq_(lhs, rhs)
                            }
                            z3_sys::SortKind::Seq => {
                                let lhs = StringAst::from_z3(ctx, arg0)?;
                                let rhs = StringAst::from_z3(ctx, arg1)?;
                                ctx.str_eq(lhs, rhs)
                            }
                            _ => Err(ClarirsError::ConversionError(
                                "Eq operand has unrecognized sort".to_string(),
                            )),
                        }
                    }
                    z3_sys::DeclKind::DISTINCT => {
                        if z3_sys::Z3_get_app_num_args(*z3_ctx, app) != 2 {
                            return Err(ClarirsError::ConversionError(
                                "Distinct with != 2 args not supported".to_string(),
                            ));
                        }
                        let arg0 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let arg1 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"))?;
                        let sort = z3_sys::Z3_get_sort(*z3_ctx, *arg0).expect("Z3_get_sort returned null");
                        let sort_kind = z3_sys::Z3_get_sort_kind(*z3_ctx, sort);

                        match sort_kind {
                            z3_sys::SortKind::Bool => {
                                let lhs = BoolAst::from_z3(ctx, arg0)?;
                                let rhs = BoolAst::from_z3(ctx, arg1)?;
                                ctx.neq(lhs, rhs)
                            }
                            z3_sys::SortKind::BV => {
                                let lhs = BitVecAst::from_z3(ctx, arg0)?;
                                let rhs = BitVecAst::from_z3(ctx, arg1)?;
                                ctx.neq(lhs, rhs)
                            }
                            z3_sys::SortKind::FloatingPoint => {
                                let lhs = FloatAst::from_z3(ctx, arg0)?;
                                let rhs = FloatAst::from_z3(ctx, arg1)?;
                                ctx.fp_neq(lhs, rhs)
                            }
                            z3_sys::SortKind::Seq => {
                                let lhs = StringAst::from_z3(ctx, arg0)?;
                                let rhs = StringAst::from_z3(ctx, arg1)?;
                                ctx.str_neq(lhs, rhs)
                            }
                            _ => Err(ClarirsError::ConversionError(
                                "Distinct operand has unrecognized sort".to_string(),
                            )),
                        }
                    }
                    z3_sys::DeclKind::ULT
                    | z3_sys::DeclKind::ULEQ
                    | z3_sys::DeclKind::UGT
                    | z3_sys::DeclKind::UGEQ
                    | z3_sys::DeclKind::SLT
                    | z3_sys::DeclKind::SLEQ
                    | z3_sys::DeclKind::SGT
                    | z3_sys::DeclKind::SGEQ => {
                        let arg0 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let arg1 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"))?;

                        // Convert both arguments
                        let a = BitVecAst::from_z3(ctx, arg0)?;
                        let b = BitVecAst::from_z3(ctx, arg1)?;

                        // Create the appropriate operation
                        match decl_kind {
                            z3_sys::DeclKind::ULT => ctx.ult(a, b),
                            z3_sys::DeclKind::ULEQ => ctx.ule(a, b),
                            z3_sys::DeclKind::UGT => ctx.ugt(a, b),
                            z3_sys::DeclKind::UGEQ => ctx.uge(a, b),
                            z3_sys::DeclKind::SLT => ctx.slt(a, b),
                            z3_sys::DeclKind::SLEQ => ctx.sle(a, b),
                            z3_sys::DeclKind::SGT => ctx.sgt(a, b),
                            z3_sys::DeclKind::SGEQ => ctx.sge(a, b),
                            _ => unreachable!(),
                        }
                    }
                    // FP comparisons
                    z3_sys::DeclKind::FPA_EQ
                    | z3_sys::DeclKind::FPA_LT
                    | z3_sys::DeclKind::FPA_LE
                    | z3_sys::DeclKind::FPA_GT
                    | z3_sys::DeclKind::FPA_GE => {
                        let arg0 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let arg1 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"))?;

                        let a = FloatAst::from_z3(ctx, arg0)?;
                        let b = FloatAst::from_z3(ctx, arg1)?;

                        match decl_kind {
                            z3_sys::DeclKind::FPA_EQ => ctx.fp_eq(a, b),
                            z3_sys::DeclKind::FPA_LT => ctx.fp_lt(a, b),
                            z3_sys::DeclKind::FPA_LE => ctx.fp_leq(a, b),
                            z3_sys::DeclKind::FPA_GT => ctx.fp_gt(a, b),
                            z3_sys::DeclKind::FPA_GE => ctx.fp_geq(a, b),
                            _ => unreachable!(),
                        }
                    }
                    z3_sys::DeclKind::FPA_IS_NAN => {
                        let arg0 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let a = FloatAst::from_z3(ctx, arg0)?;
                        ctx.fp_is_nan(a)
                    }
                    z3_sys::DeclKind::FPA_IS_INF => {
                        let arg0 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let a = FloatAst::from_z3(ctx, arg0)?;
                        ctx.fp_is_inf(a)
                    }

                    // String predicates
                    z3_sys::DeclKind::SEQ_CONTAINS
                    | z3_sys::DeclKind::SEQ_PREFIX
                    | z3_sys::DeclKind::SEQ_SUFFIX => {
                        let arg0 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let arg1 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"))?;

                        let a = StringAst::from_z3(ctx, arg0)?;
                        let b = StringAst::from_z3(ctx, arg1)?;

                        match decl_kind {
                            z3_sys::DeclKind::SEQ_CONTAINS => ctx.str_contains(a, b),
                            z3_sys::DeclKind::SEQ_PREFIX => ctx.str_prefix_of(a, b),
                            z3_sys::DeclKind::SEQ_SUFFIX => ctx.str_suffix_of(a, b),
                            _ => unreachable!(),
                        }
                    }

                    z3_sys::DeclKind::ITE => {
                        let cond = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let then = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"))?;
                        let else_ = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 2).expect("Z3_get_app_arg returned null"))?;
                        let cond = BoolAst::from_z3(ctx, cond)?;
                        let then = BoolAst::from_z3(ctx, then)?;
                        let else_ = BoolAst::from_z3(ctx, else_)?;
                        ctx.ite(cond, then, else_)
                    }
                    z3_sys::DeclKind::UNINTERPRETED => {
                        // Verify it's a boolean
                        let sort = z3_sys::Z3_get_sort(*z3_ctx, *ast).expect("Z3_get_sort returned null");
                        let bool_sort = z3_sys::Z3_mk_bool_sort(*z3_ctx).expect("Z3_mk_bool_sort returned null");
                        if sort != bool_sort {
                            return Err(ClarirsError::ConversionError(
                                "expected a boolean".to_string(),
                            ));
                        }
                        let sym = z3_sys::Z3_get_decl_name(*z3_ctx, decl).expect("Z3_get_decl_name returned null");
                        let name = z3_sys::Z3_get_symbol_string(*z3_ctx, sym);
                        let name = std::ffi::CStr::from_ptr(name).to_str().unwrap();
                        ctx.bools(name)
                    }
                    _ => {
                        let decl_name =
                            CStr::from_ptr(z3_sys::Z3_func_decl_to_string(*z3_ctx, decl) as *mut i8)
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
