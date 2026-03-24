use clarirs_core::{ast::bitvec::BitVecOpExt, prelude::*};

use super::AstExtZ3;
use crate::{Z3_CONTEXT, astext::child, check_z3_error, rc::RcAst};

pub(crate) fn to_z3(ast: &BitVecAst, children: &[RcAst]) -> Result<RcAst, ClarirsError> {
    Z3_CONTEXT.with(|&z3_ctx| unsafe {
        Ok(match ast.op() {
            BitVecOp::BVS(s, w) => {
                let s_cstr = std::ffi::CString::new(s.as_str()).unwrap();
                let sym = z3_sys::Z3_mk_string_symbol(z3_ctx, s_cstr.as_ptr()).expect("Z3_mk_string_symbol returned null");
                let sort = z3_sys::Z3_mk_bv_sort(z3_ctx, *w).expect("Z3_mk_bv_sort returned null");
                RcAst::try_from(z3_sys::Z3_mk_const(z3_ctx, sym, sort).expect("Z3_mk_const returned null"))?
            }
            BitVecOp::BVV(v) => {
                let sort = z3_sys::Z3_mk_bv_sort(z3_ctx, v.len()).expect("Z3_mk_bv_sort returned null");
                let numeral = v.to_biguint().to_string();
                let numeral_cstr = std::ffi::CString::new(numeral).unwrap();
                RcAst::try_from(z3_sys::Z3_mk_numeral(z3_ctx, numeral_cstr.as_ptr(), sort).expect("Z3_mk_numeral returned null"))?
            }
            BitVecOp::Not(..) => unop!(z3_ctx, children, Z3_mk_bvnot),
            BitVecOp::Neg(..) => unop!(z3_ctx, children, Z3_mk_bvneg),
            BitVecOp::And(..) => naryop!(z3_ctx, children, Z3_mk_bvand),
            BitVecOp::Or(..) => naryop!(z3_ctx, children, Z3_mk_bvor),
            BitVecOp::Xor(..) => naryop!(z3_ctx, children, Z3_mk_bvxor),
            BitVecOp::Add(..) => naryop!(z3_ctx, children, Z3_mk_bvadd),
            BitVecOp::Sub(..) => binop!(z3_ctx, children, Z3_mk_bvsub),
            BitVecOp::Mul(..) => naryop!(z3_ctx, children, Z3_mk_bvmul),
            BitVecOp::UDiv(..) => binop!(z3_ctx, children, Z3_mk_bvudiv),
            BitVecOp::SDiv(..) => binop!(z3_ctx, children, Z3_mk_bvsdiv),
            BitVecOp::URem(..) => binop!(z3_ctx, children, Z3_mk_bvurem),
            BitVecOp::SRem(..) => binop!(z3_ctx, children, Z3_mk_bvsrem),
            BitVecOp::ShL(..) => binop!(z3_ctx, children, Z3_mk_bvshl),
            BitVecOp::LShR(..) => binop!(z3_ctx, children, Z3_mk_bvlshr),
            BitVecOp::AShR(..) => binop!(z3_ctx, children, Z3_mk_bvashr),
            BitVecOp::RotateLeft(..) => binop!(z3_ctx, children, Z3_mk_ext_rotate_left),
            BitVecOp::RotateRight(..) => binop!(z3_ctx, children, Z3_mk_ext_rotate_right),
            BitVecOp::ZeroExt(_, i) => {
                RcAst::try_from(z3_sys::Z3_mk_zero_ext(z3_ctx, *i, **child(children, 0)?).expect("Z3_mk_zero_ext returned null"))?
            }
            BitVecOp::SignExt(_, i) => {
                RcAst::try_from(z3_sys::Z3_mk_sign_ext(z3_ctx, *i, **child(children, 0)?).expect("Z3_mk_sign_ext returned null"))?
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
                RcAst::try_from(z3_sys::Z3_mk_extract(z3_ctx, *high, *low, **a).expect("Z3_mk_extract returned null"))?
            }
            BitVecOp::Concat(args) => {
                // Z3's concat constructor is binary, so we chain them
                if args.is_empty() {
                    return Err(ClarirsError::InvalidArguments(
                        "Concat requires at least one argument".to_string(),
                    ));
                }
                let mut result = child(children, 0)?.clone();
                for i in 1..children.len() {
                    result =
                        RcAst::try_from(z3_sys::Z3_mk_concat(z3_ctx, *result, **child(children, i)?).expect("Z3_mk_concat returned null"))?;
                }
                result
            }
            BitVecOp::ByteReverse(a) => {
                let size = a.size();
                if size == 0 || size % 8 != 0 {
                    return Err(ClarirsError::ConversionError(
                        "reverse only supports bitvectors with size multiple of 8".to_string(),
                    ));
                }

                let child_z3 = child(children, 0)?;
                let num_bytes = size / 8;

                // Extract the last byte (lowest bits) as the initial accumulator
                let mut result = RcAst::try_from(z3_sys::Z3_mk_extract(z3_ctx, 7, 0, **child_z3).expect("Z3_mk_extract returned null"))?;

                // Extract remaining bytes in reverse order and concat
                for i in 1..num_bytes {
                    let high = (i + 1) * 8 - 1;
                    let low = i * 8;
                    let byte = RcAst::try_from(z3_sys::Z3_mk_extract(z3_ctx, high, low, **child_z3).expect("Z3_mk_extract returned null"))?;
                    result = RcAst::try_from(z3_sys::Z3_mk_concat(z3_ctx, *result, *byte).expect("Z3_mk_concat returned null"))?;
                }

                result
            }
            BitVecOp::ITE(..) => {
                let cond = child(children, 0)?;
                let then = child(children, 1)?;
                let else_ = child(children, 2)?;
                RcAst::try_from(z3_sys::Z3_mk_ite(z3_ctx, **cond, **then, **else_).expect("Z3_mk_ite returned null"))?
            }
            BitVecOp::FpToIEEEBV(..) => {
                let a = child(children, 0)?;
                RcAst::try_from(z3_sys::Z3_mk_fpa_to_ieee_bv(z3_ctx, **a).expect("Z3_mk_fpa_to_ieee_bv returned null"))?
            }
            BitVecOp::FpToUBV(_, size, rm) => {
                let rm_ast = super::float::fprm_to_z3(*rm)?;
                let a = child(children, 0)?;
                RcAst::try_from(z3_sys::Z3_mk_fpa_to_ubv(z3_ctx, *rm_ast, **a, *size).expect("Z3_mk_fpa_to_ubv returned null"))?
            }
            BitVecOp::FpToSBV(_, size, rm) => {
                let rm_ast = super::float::fprm_to_z3(*rm)?;
                let a = child(children, 0)?;
                RcAst::try_from(z3_sys::Z3_mk_fpa_to_sbv(z3_ctx, *rm_ast, **a, *size).expect("Z3_mk_fpa_to_sbv returned null"))?
            }
            BitVecOp::StrLen(..) => {
                let a = child(children, 0)?;
                let str_len = RcAst::try_from(z3_sys::Z3_mk_seq_length(z3_ctx, **a).expect("Z3_mk_seq_length returned null"))?;
                RcAst::try_from(z3_sys::Z3_mk_int2bv(z3_ctx, 64, *str_len).expect("Z3_mk_int2bv returned null"))?
            }
            BitVecOp::StrIndexOf(..) => {
                let haystack = child(children, 0)?;
                let needle = child(children, 1)?;
                let offset_bv = child(children, 2)?;
                let offset_int = RcAst::try_from(z3_sys::Z3_mk_bv2int(z3_ctx, **offset_bv, false).expect("Z3_mk_bv2int returned null"))?;
                let index_int =
                    RcAst::try_from(z3_sys::Z3_mk_seq_index(z3_ctx, **haystack, **needle, *offset_int).expect("Z3_mk_seq_index returned null"))?;
                RcAst::try_from(z3_sys::Z3_mk_int2bv(z3_ctx, 64, *index_int).expect("Z3_mk_int2bv returned null"))?
            }
            BitVecOp::StrToBV(..) => {
                let a = child(children, 0)?;
                let int_val = RcAst::try_from(z3_sys::Z3_mk_str_to_int(z3_ctx, **a).expect("Z3_mk_str_to_int returned null"))?;
                RcAst::try_from(z3_sys::Z3_mk_int2bv(z3_ctx, 64, *int_val).expect("Z3_mk_int2bv returned null"))?
            }
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
        let ast_kind = z3_sys::Z3_get_ast_kind(*z3_ctx, *ast);
        match ast_kind {
            z3_sys::AstKind::Numeral => {
                let numeral_string = z3_sys::Z3_get_numeral_string(*z3_ctx, *ast);
                let numeral_str = std::ffi::CStr::from_ptr(numeral_string).to_str().unwrap();
                let sort = z3_sys::Z3_get_sort(*z3_ctx, *ast).expect("Z3_get_sort returned null");
                let sort_num = z3_sys::Z3_get_bv_sort_size(*z3_ctx, sort);
                let biguint = BitVec::from_str(numeral_str, sort_num).unwrap();
                ctx.bvv(biguint)
            }
            z3_sys::AstKind::App => {
                let app = z3_sys::Z3_to_app(*z3_ctx, *ast).expect("Z3_to_app returned null");
                let decl = z3_sys::Z3_get_app_decl(*z3_ctx, app).expect("Z3_get_app_decl returned null");
                let decl_kind = z3_sys::Z3_get_decl_kind(*z3_ctx, decl);
                let sort = z3_sys::Z3_get_sort(*z3_ctx, *ast).expect("Z3_get_sort returned null");
                let width = z3_sys::Z3_get_bv_sort_size(*z3_ctx, sort);

                match decl_kind {
                    z3_sys::DeclKind::UNINTERPRETED => {
                        let sym = z3_sys::Z3_get_decl_name(*z3_ctx, decl).expect("Z3_get_decl_name returned null");
                        let name = z3_sys::Z3_get_symbol_string(*z3_ctx, sym);
                        let name = std::ffi::CStr::from_ptr(name).to_str().unwrap();
                        ctx.bvs(name, width as u32)
                    }
                    z3_sys::DeclKind::BNOT => {
                        let arg = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let inner = BitVecAst::from_z3(ctx, arg)?;
                        ctx.not(inner)
                    }
                    z3_sys::DeclKind::BNEG => {
                        let arg = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let inner = BitVecAst::from_z3(ctx, arg)?;
                        ctx.neg(inner)
                    }
                    z3_sys::DeclKind::BAND
                    | z3_sys::DeclKind::BOR
                    | z3_sys::DeclKind::BXOR
                    | z3_sys::DeclKind::BADD
                    | z3_sys::DeclKind::BMUL => {
                        // N-ary ops: collect all args into a Vec
                        let num_args = z3_sys::Z3_get_app_num_args(*z3_ctx, app);
                        let mut args = Vec::with_capacity(num_args as usize);
                        for i in 0..num_args {
                            let arg = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, i).expect("Z3_get_app_arg returned null"))?;
                            args.push(BitVecAst::from_z3(ctx, arg)?);
                        }
                        match decl_kind {
                            z3_sys::DeclKind::BAND => ctx.bv_and_many(args),
                            z3_sys::DeclKind::BOR => ctx.bv_or_many(args),
                            z3_sys::DeclKind::BXOR => ctx.bv_xor_many(args),
                            z3_sys::DeclKind::BADD => ctx.add_many(args),
                            z3_sys::DeclKind::BMUL => ctx.mul_many(args),
                            _ => unreachable!(),
                        }
                    }
                    z3_sys::DeclKind::BSUB
                    | z3_sys::DeclKind::BUDIV
                    | z3_sys::DeclKind::BSDIV
                    | z3_sys::DeclKind::BUREM
                    | z3_sys::DeclKind::BSREM
                    | z3_sys::DeclKind::BSHL
                    | z3_sys::DeclKind::BLSHR
                    | z3_sys::DeclKind::BASHR => {
                        let arg0 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let arg1 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"))?;
                        let a = BitVecAst::from_z3(ctx, arg0)?;
                        let b = BitVecAst::from_z3(ctx, arg1)?;
                        match decl_kind {
                            z3_sys::DeclKind::BSUB => ctx.sub(a, b),
                            z3_sys::DeclKind::BUDIV => ctx.udiv(a, b),
                            z3_sys::DeclKind::BSDIV => ctx.sdiv(a, b),
                            z3_sys::DeclKind::BUREM => ctx.urem(a, b),
                            z3_sys::DeclKind::BSREM => ctx.srem(a, b),
                            z3_sys::DeclKind::BSHL => ctx.shl(a, b),
                            z3_sys::DeclKind::BLSHR => ctx.lshr(a, b),
                            z3_sys::DeclKind::BASHR => ctx.ashr(a, b),
                            _ => unreachable!(),
                        }
                    }
                    z3_sys::DeclKind::EXT_ROTATE_LEFT | z3_sys::DeclKind::EXT_ROTATE_RIGHT => {
                        let arg0 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let arg1 = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"))?;
                        let a = BitVecAst::from_z3(ctx, arg0)?;
                        let b = BitVecAst::from_z3(ctx, arg1)?;
                        match decl_kind {
                            z3_sys::DeclKind::EXT_ROTATE_LEFT => ctx.rotate_left(a, b),
                            z3_sys::DeclKind::EXT_ROTATE_RIGHT => ctx.rotate_right(a, b),
                            _ => unreachable!(),
                        }
                    }
                    z3_sys::DeclKind::ZERO_EXT | z3_sys::DeclKind::SIGN_EXT => {
                        let arg = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let inner = BitVecAst::from_z3(ctx, arg)?;
                        let i = z3_sys::Z3_get_decl_int_parameter(*z3_ctx, decl, 0) as u32;
                        match decl_kind {
                            z3_sys::DeclKind::ZERO_EXT => ctx.zero_ext(&inner, i),
                            z3_sys::DeclKind::SIGN_EXT => ctx.sign_ext(inner, i),
                            _ => unreachable!(),
                        }
                    }
                    z3_sys::DeclKind::EXTRACT => {
                        let arg = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let inner = BitVecAst::from_z3(ctx, arg)?;
                        let high = z3_sys::Z3_get_decl_int_parameter(*z3_ctx, decl, 0) as u32;
                        let low = z3_sys::Z3_get_decl_int_parameter(*z3_ctx, decl, 1) as u32;
                        ctx.extract(inner, high, low)
                    }
                    z3_sys::DeclKind::CONCAT => {
                        let num_args = z3_sys::Z3_get_app_num_args(*z3_ctx, app);
                        let mut concat_args = Vec::with_capacity(num_args as usize);
                        for i in 0..num_args {
                            let arg = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, i).expect("Z3_get_app_arg returned null"))?;
                            let val = BitVecAst::from_z3(ctx, arg)?;
                            concat_args.push(val);
                        }
                        ctx.concat(concat_args)
                    }
                    z3_sys::DeclKind::ITE => {
                        let cond = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                        let then = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"))?;
                        let else_ = RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 2).expect("Z3_get_app_arg returned null"))?;
                        let cond = BoolAst::from_z3(ctx, cond)?;
                        let then = BitVecAst::from_z3(ctx, then)?;
                        let else_ = BitVecAst::from_z3(ctx, else_)?;
                        ctx.ite(cond, then, else_)
                    }
                    // Special case for bv2int used in string operations
                    z3_sys::DeclKind::INT2BV => {
                        let inner_int = z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null");
                        let inner_ast_kind = z3_sys::Z3_get_ast_kind(*z3_ctx, *ast);
                        match inner_ast_kind {
                            z3_sys::AstKind::Numeral => {
                                let numeral_string = z3_sys::Z3_get_numeral_string(*z3_ctx, inner_int);
                                let numeral_str =
                                    std::ffi::CStr::from_ptr(numeral_string).to_str().unwrap();
                                let sort = z3_sys::Z3_get_sort(*z3_ctx, inner_int).expect("Z3_get_sort returned null");
                                let sort_num = z3_sys::Z3_get_bv_sort_size(*z3_ctx, sort);
                                let biguint = BitVec::from_str(numeral_str, sort_num).unwrap();
                                ctx.bvv(biguint)
                            }
                            z3_sys::AstKind::App => {
                                let app = z3_sys::Z3_to_app(*z3_ctx, inner_int).expect("Z3_to_app returned null");
                                let decl = z3_sys::Z3_get_app_decl(*z3_ctx, app).expect("Z3_get_app_decl returned null");
                                let decl_kind = z3_sys::Z3_get_decl_kind(*z3_ctx, decl);

                                match decl_kind {
                                    z3_sys::DeclKind::BV2INT => {
                                        let arg =
                                            RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                                        BitVecAst::from_z3(ctx, arg)
                                    }
                                    z3_sys::DeclKind::SEQ_INDEX => {
                                        // int2bv(seq.indexof(haystack, needle, offset))
                                        let arg0 =
                                            RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                                        let arg1 =
                                            RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 1).expect("Z3_get_app_arg returned null"))?;
                                        let arg2 =
                                            RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 2).expect("Z3_get_app_arg returned null"))?;
                                        let haystack = StringAst::from_z3(ctx, arg0)?;
                                        let needle = StringAst::from_z3(ctx, arg1)?;
                                        // offset is an int, convert to bv
                                        let offset_bv =
                                            RcAst::try_from(z3_sys::Z3_mk_int2bv(*z3_ctx, 64, *arg2).expect("Z3_mk_int2bv returned null"))?;
                                        let offset_simplified =
                                            RcAst::try_from(z3_sys::Z3_simplify(*z3_ctx, *offset_bv).expect("Z3_simplify returned null"))?;
                                        let offset = BitVecAst::from_z3(ctx, offset_simplified)?;
                                        ctx.str_index_of(haystack, needle, offset)
                                    }
                                    z3_sys::DeclKind::STR_TO_INT => {
                                        // int2bv(str.to_int(s))
                                        let arg0 =
                                            RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                                        let s = StringAst::from_z3(ctx, arg0)?;
                                        ctx.str_to_bv(s)
                                    }
                                    z3_sys::DeclKind::SEQ_LENGTH => {
                                        // int2bv(seq.len(s))
                                        let arg0 =
                                            RcAst::try_from(z3_sys::Z3_get_app_arg(*z3_ctx, app, 0).expect("Z3_get_app_arg returned null"))?;
                                        let s = StringAst::from_z3(ctx, arg0)?;
                                        ctx.str_len(s)
                                    }
                                    _ => Err(ClarirsError::ConversionError(format!(
                                        "unexpected inner decl kind in Int2bv: {:?}",
                                        decl_kind,
                                    ))),
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
