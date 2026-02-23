use clarirs_core::{
    ast::bitvec::{BitVecAstExt, BitVecOpExt},
    prelude::*,
};
use clarirs_z3_sys as z3;

use super::AstExtZ3;
use crate::{astext::child, check_z3_error, rc::RcAst, Z3_CONTEXT};

pub(crate) fn to_z3(ast: &BitVecAst, children: &[RcAst]) -> Result<RcAst, ClarirsError> {
    Z3_CONTEXT.with(|&z3_ctx| unsafe {
        Ok(match ast.op() {
            BitVecOp::BVS(s, w) => {
                let s_cstr = std::ffi::CString::new(s.as_str()).unwrap();
                let sym = z3::mk_string_symbol(z3_ctx, s_cstr.as_ptr());
                let sort = z3::mk_bv_sort(z3_ctx, *w);
                RcAst::try_from(z3::mk_const(z3_ctx, sym, sort))?
            }
            BitVecOp::BVV(v) => {
                let sort = z3::mk_bv_sort(z3_ctx, v.len());
                let numeral = v.to_biguint().to_string();
                let numeral_cstr = std::ffi::CString::new(numeral).unwrap();
                RcAst::try_from(z3::mk_numeral(z3_ctx, numeral_cstr.as_ptr(), sort))?
            }
            BitVecOp::Not(..) => unop!(z3_ctx, children, mk_bvnot),
            BitVecOp::Neg(..) => unop!(z3_ctx, children, mk_bvneg),
            BitVecOp::And(..) => binop!(z3_ctx, children, mk_bvand),
            BitVecOp::Or(..) => binop!(z3_ctx, children, mk_bvor),
            BitVecOp::Xor(..) => binop!(z3_ctx, children, mk_bvxor),
            BitVecOp::Add(..) => binop!(z3_ctx, children, mk_bvadd),
            BitVecOp::Sub(..) => binop!(z3_ctx, children, mk_bvsub),
            BitVecOp::Mul(..) => binop!(z3_ctx, children, mk_bvmul),
            BitVecOp::UDiv(..) => binop!(z3_ctx, children, mk_bvudiv),
            BitVecOp::SDiv(..) => binop!(z3_ctx, children, mk_bvsdiv),
            BitVecOp::URem(..) => binop!(z3_ctx, children, mk_bvurem),
            BitVecOp::SRem(..) => binop!(z3_ctx, children, mk_bvsrem),
            BitVecOp::ShL(..) => binop!(z3_ctx, children, mk_bvshl),
            BitVecOp::LShR(..) => binop!(z3_ctx, children, mk_bvlshr),
            BitVecOp::AShR(..) => binop!(z3_ctx, children, mk_bvashr),
            BitVecOp::RotateLeft(..) => binop!(z3_ctx, children, mk_ext_rotate_left),
            BitVecOp::RotateRight(..) => binop!(z3_ctx, children, mk_ext_rotate_right),
            BitVecOp::ZeroExt(_, i) => {
                RcAst::try_from(z3::mk_zero_ext(z3_ctx, *i, **child(children, 0)?))?
            }
            BitVecOp::SignExt(_, i) => {
                RcAst::try_from(z3::mk_sign_ext(z3_ctx, *i, **child(children, 0)?))?
            }
            BitVecOp::Extract(a, high, low) => {
                if high >= &a.size() {
                    return Err(ClarirsError::ConversionError(
                        "high index is greater than bitvector size".to_string(),
                    ));
                }
                if low >= &a.size() {
                    return Err(ClarirsError::ConversionError(
                        "low index is greater than bitvector size".to_string(),
                    ));
                }
                if low > high {
                    return Err(ClarirsError::ConversionError(
                        "low index is greater than high index".to_string(),
                    ));
                }
                let a = child(children, 0)?;
                RcAst::try_from(z3::mk_extract(z3_ctx, *high, *low, **a))?
            }
            BitVecOp::Concat(args) => {
                // Z3's concat constructor is binary, so we chain them
                if args.is_empty() {
                    return Err(ClarirsError::InvalidArgumentsWithMessage(
                        "Concat requires at least one argument".to_string(),
                    ));
                }
                let mut result = child(children, 0)?.clone();
                for i in 1..children.len() {
                    result =
                        RcAst::try_from(z3::mk_concat(z3_ctx, *result, **child(children, i)?))?;
                }
                result
            }
            BitVecOp::ByteReverse(a) => {
                if a.size() == 0 || a.size() % 8 != 0 {
                    return Err(ClarirsError::ConversionError(
                        "reverse only supports bitvectors with size multiple of 8".to_string(),
                    ));
                }

                let bytes = a.chop(8)?;
                let reversed = bytes.iter().rev().collect::<Vec<_>>();

                let mut acc: Option<BitVecAst> = None;

                for byte in reversed {
                    acc = match acc {
                        Some(inner) => Some(ast.context().concat2(inner, byte)?),
                        None => Some(byte.clone()),
                    };
                }

                // FIXME: recursion
                acc.unwrap().to_z3()?
            }
            BitVecOp::ITE(..) => {
                let cond = child(children, 0)?;
                let then = child(children, 1)?;
                let else_ = child(children, 2)?;
                RcAst::try_from(z3::mk_ite(z3_ctx, **cond, **then, **else_))?
            }
            BitVecOp::FpToIEEEBV(..) => {
                let a = child(children, 0)?;
                RcAst::try_from(z3::mk_fpa_to_ieee_bv(z3_ctx, **a))?
            }
            BitVecOp::FpToUBV(_, size, rm) => {
                let rm_ast = super::float::fprm_to_z3(*rm)?;
                let a = child(children, 0)?;
                RcAst::try_from(z3::mk_fpa_to_ubv(z3_ctx, *rm_ast, **a, *size))?
            }
            BitVecOp::FpToSBV(_, size, rm) => {
                let rm_ast = super::float::fprm_to_z3(*rm)?;
                let a = child(children, 0)?;
                RcAst::try_from(z3::mk_fpa_to_sbv(z3_ctx, *rm_ast, **a, *size))?
            }
            BitVecOp::StrLen(..) => {
                let a = child(children, 0)?;
                let str_len = RcAst::try_from(z3::mk_seq_length(z3_ctx, **a))?;
                RcAst::try_from(z3::mk_int2bv(z3_ctx, 64, *str_len))?
            }
            BitVecOp::StrIndexOf(..) => todo!("StrIndexOf"),
            BitVecOp::StrToBV(..) => todo!("StrToBV"),
            BitVecOp::Union(..) | BitVecOp::Intersection(..) | BitVecOp::Widen(..) => {
                // These are not supported in Z3
                return Err(ClarirsError::ConversionError(
                    "vsa types are not currently supported in the z3 backend".to_string(),
                ));
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
) -> Result<BitVecAst<'c>, ClarirsError> {
    Z3_CONTEXT.with(|z3_ctx| unsafe {
        let ast = ast.into();
        let ast_kind = z3::get_ast_kind(*z3_ctx, *ast);
        match ast_kind {
            z3::AstKind::Numeral => {
                let numeral_string = z3::get_numeral_string(*z3_ctx, *ast);
                let numeral_str = std::ffi::CStr::from_ptr(numeral_string).to_str().unwrap();
                let sort = z3::get_sort(*z3_ctx, *ast);
                let sort_num = z3::get_bv_sort_size(*z3_ctx, sort);
                let biguint = BitVec::from_str(numeral_str, sort_num).unwrap();
                ctx.bvv(biguint)
            }
            z3::AstKind::App => {
                let app = z3::to_app(*z3_ctx, *ast);
                let decl = z3::get_app_decl(*z3_ctx, app);
                let decl_kind = z3::get_decl_kind(*z3_ctx, decl);
                let sort = z3::get_sort(*z3_ctx, *ast);
                let width = z3::get_bv_sort_size(*z3_ctx, sort);

                match decl_kind {
                    z3::DeclKind::Uninterpreted => {
                        let sym = z3::get_decl_name(*z3_ctx, decl);
                        let name = z3::get_symbol_string(*z3_ctx, sym);
                        let name = std::ffi::CStr::from_ptr(name).to_str().unwrap();
                        ctx.bvs(name, width as u32)
                    }
                    z3::DeclKind::Bnot => {
                        let arg = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let inner = BitVecAst::from_z3(ctx, arg)?;
                        ctx.not(inner)
                    }
                    z3::DeclKind::Bneg => {
                        let arg = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let inner = BitVecAst::from_z3(ctx, arg)?;
                        ctx.neg(inner)
                    }
                    z3::DeclKind::Band
                    | z3::DeclKind::Bor
                    | z3::DeclKind::Bxor
                    | z3::DeclKind::Badd
                    | z3::DeclKind::Bsub
                    | z3::DeclKind::Bmul
                    | z3::DeclKind::Budiv
                    | z3::DeclKind::Bsdiv
                    | z3::DeclKind::Burem
                    | z3::DeclKind::Bsrem
                    | z3::DeclKind::Bshl
                    | z3::DeclKind::Blshr
                    | z3::DeclKind::Bashr => {
                        let num_args = z3::get_app_num_args(*z3_ctx, app);
                        if num_args != 2 {
                            return Err(ClarirsError::ConversionError(
                                "Expected binary operation to have 2 arguments".to_string(),
                            ));
                        }

                        let arg0 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let arg1 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 1))?;
                        let a = BitVecAst::from_z3(ctx, arg0)?;
                        let b = BitVecAst::from_z3(ctx, arg1)?;

                        // HACK: Size adjustment
                        // Z3 sometimes returns bitvectors of different sizes for operations.
                        let max_size = a.size().max(b.size());
                        let a = if a.size() < max_size {
                            ctx.zero_ext(&a, max_size - a.size())?
                        } else {
                            a
                        };
                        let b = if b.size() < max_size {
                            ctx.zero_ext(&b, max_size - b.size())?
                        } else {
                            b
                        };

                        match decl_kind {
                            z3::DeclKind::Band => ctx.bv_and(a, b),
                            z3::DeclKind::Bor => ctx.bv_or(a, b),
                            z3::DeclKind::Bxor => ctx.xor(a, b),
                            z3::DeclKind::Badd => ctx.add(a, b),
                            z3::DeclKind::Bsub => ctx.sub(a, b),
                            z3::DeclKind::Bmul => ctx.mul(a, b),
                            z3::DeclKind::Budiv => ctx.udiv(a, b),
                            z3::DeclKind::Bsdiv => ctx.sdiv(a, b),
                            z3::DeclKind::Burem => ctx.urem(a, b),
                            z3::DeclKind::Bsrem => ctx.srem(a, b),
                            z3::DeclKind::Bshl => ctx.shl(a, b),
                            z3::DeclKind::Blshr => ctx.lshr(a, b),
                            z3::DeclKind::Bashr => ctx.ashr(a, b),
                            _ => unreachable!(),
                        }
                    }
                    z3::DeclKind::ExtRotateLeft | z3::DeclKind::ExtRotateRight => {
                        let arg0 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let arg1 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 1))?;
                        let a = BitVecAst::from_z3(ctx, arg0)?;
                        let b = BitVecAst::from_z3(ctx, arg1)?;
                        match decl_kind {
                            z3::DeclKind::ExtRotateLeft => ctx.rotate_left(a, b),
                            z3::DeclKind::ExtRotateRight => ctx.rotate_right(a, b),
                            _ => unreachable!(),
                        }
                    }
                    z3::DeclKind::ZeroExt | z3::DeclKind::SignExt => {
                        let arg = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let inner = BitVecAst::from_z3(ctx, arg)?;
                        let i = z3::get_decl_int_parameter(*z3_ctx, decl, 0) as u32;
                        match decl_kind {
                            z3::DeclKind::ZeroExt => ctx.zero_ext(&inner, i),
                            z3::DeclKind::SignExt => ctx.sign_ext(inner, i),
                            _ => unreachable!(),
                        }
                    }
                    z3::DeclKind::Extract => {
                        let arg = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let inner = BitVecAst::from_z3(ctx, arg)?;
                        let high = z3::get_decl_int_parameter(*z3_ctx, decl, 0) as u32;
                        let low = z3::get_decl_int_parameter(*z3_ctx, decl, 1) as u32;
                        ctx.extract(inner, high, low)
                    }
                    z3::DeclKind::Concat => {
                        let num_args = z3::get_app_num_args(*z3_ctx, app);
                        let mut concat_args = Vec::with_capacity(num_args as usize);
                        for i in 0..num_args {
                            let arg = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, i))?;
                            let val = BitVecAst::from_z3(ctx, arg)?;
                            concat_args.push(val);
                        }
                        ctx.concat(concat_args)
                    }
                    z3::DeclKind::Ite => {
                        let cond = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let then = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 1))?;
                        let else_ = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 2))?;
                        let cond = BoolAst::from_z3(ctx, cond)?;
                        let then = BitVecAst::from_z3(ctx, then)?;
                        let else_ = BitVecAst::from_z3(ctx, else_)?;
                        ctx.ite(cond, then, else_)
                    }
                    // Special case for bv2int used in string operations
                    z3::DeclKind::Int2bv => {
                        let inner_int = z3::get_app_arg(*z3_ctx, app, 0);
                        let inner_ast_kind = z3::get_ast_kind(*z3_ctx, *ast);
                        match inner_ast_kind {
                            z3::AstKind::Numeral => {
                                let numeral_string = z3::get_numeral_string(*z3_ctx, inner_int);
                                let numeral_str =
                                    std::ffi::CStr::from_ptr(numeral_string).to_str().unwrap();
                                let sort = z3::get_sort(*z3_ctx, inner_int);
                                let sort_num = z3::get_bv_sort_size(*z3_ctx, sort);
                                let biguint = BitVec::from_str(numeral_str, sort_num).unwrap();
                                ctx.bvv(biguint)
                            }
                            z3::AstKind::App => {
                                let app = z3::to_app(*z3_ctx, inner_int);
                                let decl = z3::get_app_decl(*z3_ctx, app);
                                let decl_kind = z3::get_decl_kind(*z3_ctx, decl);

                                match decl_kind {
                                    z3::DeclKind::Bv2int => {
                                        let arg =
                                            RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                                        BitVecAst::from_z3(ctx, arg)
                                    }
                                    _ => Err(ClarirsError::ConversionError(
                                        "expected a Bv2int".to_string(),
                                    )),
                                }
                            }
                            _ => Err(ClarirsError::ConversionError(
                                "expected a numeral or bv2int".to_string(),
                            )),
                        }
                    }
                    _ => Err(ClarirsError::ConversionError(
                        "Failed converting from z3: unknown decl kind for bitvec".to_string(),
                    )),
                }
            }
            _ => Err(ClarirsError::ConversionError(
                "Failed converting from z3: unknown ast kind for bitvec".to_string(),
            )),
        }
    })
}
