use std::ffi::CStr;

use crate::{astext::child, check_z3_error, rc::RcAst, Z3_CONTEXT};
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
                let args: Vec<_> = children.iter().map(|c| **c).collect();
                z3::mk_and(z3_ctx, args.len() as u32, args.as_ptr()).try_into()?
            }
            BooleanOp::Or(..) => {
                let args: Vec<_> = children.iter().map(|c| **c).collect();
                z3::mk_or(z3_ctx, args.len() as u32, args.as_ptr()).try_into()?
            }
            BooleanOp::Xor(..) => binop!(z3_ctx, children, mk_xor),
            BooleanOp::BoolEq(..) => binop!(z3_ctx, children, mk_eq),
            BooleanOp::BoolNeq(..) => {
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                z3::mk_distinct(z3_ctx, 2, [**a, **b].as_ptr()).try_into()?
            }
            BooleanOp::ITE(..) => {
                let cond = child(children, 0)?;
                let then = child(children, 1)?;
                let else_ = child(children, 2)?;
                z3::mk_ite(z3_ctx, **cond, **then, **else_).try_into()?
            }

            // BV operations
            BooleanOp::Eq(..) => binop!(z3_ctx, children, mk_eq),
            BooleanOp::Neq(..) => {
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                z3::mk_distinct(z3_ctx, 2, [**a, **b].as_ptr()).try_into()?
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
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                z3::mk_distinct(z3_ctx, 2, [**a, **b].as_ptr()).try_into()?
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
                let a = child(children, 0)?;
                let b = child(children, 1)?;
                z3::mk_distinct(z3_ctx, 2, [**a, **b].as_ptr()).try_into()?
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
                    z3::DeclKind::And | z3::DeclKind::Or => {
                        let num_args = z3::get_app_num_args(*z3_ctx, app);
                        let mut args = Vec::with_capacity(num_args as usize);
                        for i in 0..num_args {
                            let arg = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, i))?;
                            args.push(BoolAst::from_z3(ctx, arg)?);
                        }
                        match decl_kind {
                            z3::DeclKind::And => ctx.and(args),
                            z3::DeclKind::Or => ctx.or(args),
                            _ => unreachable!(),
                        }
                    }
                    z3::DeclKind::Xor => {
                        let arg0 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let arg1 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 1))?;
                        let a = BoolAst::from_z3(ctx, arg0)?;
                        let b = BoolAst::from_z3(ctx, arg1)?;
                        ctx.xor(a, b)
                    }
                    z3::DeclKind::Eq => {
                        let arg0 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let arg1 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 1))?;
                        let sort = z3::get_sort(*z3_ctx, *arg0);
                        let sort_kind = z3::get_sort_kind(*z3_ctx, sort);

                        match sort_kind {
                            z3::SortKind::Bool => {
                                let lhs = BoolAst::from_z3(ctx, arg0)?;
                                let rhs = BoolAst::from_z3(ctx, arg1)?;
                                ctx.eq_(lhs, rhs)
                            }
                            z3::SortKind::Bv => {
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
                    z3::DeclKind::Distinct => {
                        if z3::get_app_num_args(*z3_ctx, app) != 2 {
                            return Err(ClarirsError::ConversionError(
                                "Distinct with != 2 args not supported".to_string(),
                            ));
                        }
                        let arg0 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let arg1 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 1))?;
                        let sort = z3::get_sort(*z3_ctx, *arg0);
                        let sort_kind = z3::get_sort_kind(*z3_ctx, sort);

                        match sort_kind {
                            z3::SortKind::Bool => {
                                let lhs = BoolAst::from_z3(ctx, arg0)?;
                                let rhs = BoolAst::from_z3(ctx, arg1)?;
                                ctx.neq(lhs, rhs)
                            }
                            z3::SortKind::Bv => {
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
                    // FP comparisons
                    z3::DeclKind::FpaEq
                    | z3::DeclKind::FpaLt
                    | z3::DeclKind::FpaLe
                    | z3::DeclKind::FpaGt
                    | z3::DeclKind::FpaGe => {
                        let arg0 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let arg1 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 1))?;

                        let a = FloatAst::from_z3(ctx, arg0)?;
                        let b = FloatAst::from_z3(ctx, arg1)?;

                        match decl_kind {
                            z3::DeclKind::FpaEq => ctx.fp_eq(a, b),
                            z3::DeclKind::FpaLt => ctx.fp_lt(a, b),
                            z3::DeclKind::FpaLe => ctx.fp_leq(a, b),
                            z3::DeclKind::FpaGt => ctx.fp_gt(a, b),
                            z3::DeclKind::FpaGe => ctx.fp_geq(a, b),
                            _ => unreachable!(),
                        }
                    }
                    z3::DeclKind::FpaIsNan => {
                        let arg0 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let a = FloatAst::from_z3(ctx, arg0)?;
                        ctx.fp_is_nan(a)
                    }
                    z3::DeclKind::FpaIsInf => {
                        let arg0 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let a = FloatAst::from_z3(ctx, arg0)?;
                        ctx.fp_is_inf(a)
                    }

                    // String predicates
                    z3::DeclKind::SeqContains
                    | z3::DeclKind::SeqPrefix
                    | z3::DeclKind::SeqSuffix => {
                        let arg0 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let arg1 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 1))?;

                        let a = StringAst::from_z3(ctx, arg0)?;
                        let b = StringAst::from_z3(ctx, arg1)?;

                        match decl_kind {
                            z3::DeclKind::SeqContains => ctx.str_contains(a, b),
                            z3::DeclKind::SeqPrefix => ctx.str_prefix_of(a, b),
                            z3::DeclKind::SeqSuffix => ctx.str_suffix_of(a, b),
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
                        ctx.ite(cond, then, else_)
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
