use clarirs_core::{
    ast::bitvec::{BitVecAstExt, BitVecOpExt},
    prelude::*,
};
use clarirs_z3_sys as z3;

use super::AstExtZ3;
use crate::{Z3_CONTEXT, astext::child, check_z3_error, rc::RcAst};

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
            BitVecOp::Concat(..) => binop!(z3_ctx, children, mk_concat),
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
                        Some(inner) => Some(ast.context().concat(inner, byte)?),
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
            BitVecOp::StrLen(..) => todo!("StrLen"),
            BitVecOp::StrIndexOf(..) => todo!("StrIndexOf"),
            BitVecOp::StrToBV(..) => todo!("StrToBV"),
            BitVecOp::Union(..) | BitVecOp::Intersection(..) => {
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
                            z3::DeclKind::Band => ctx.and(a, b),
                            z3::DeclKind::Bor => ctx.or(a, b),
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
                        let arg0 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 0))?;
                        let arg1 = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, 1))?;
                        let a = BitVecAst::from_z3(ctx, arg0)?;
                        let b = BitVecAst::from_z3(ctx, arg1)?;
                        let mut res = ctx.concat(a, b)?;

                        for i in 2..num_args {
                            let arg = RcAst::try_from(z3::get_app_arg(*z3_ctx, app, i))?;
                            let val = BitVecAst::from_z3(ctx, arg)?;
                            res = ctx.concat(res, val)?;
                        }
                        Ok(res)
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

    fn verify_z3_bv_value(ast: z3::Ast, expected_value: BitVec) -> bool {
        Z3_CONTEXT.with(|z3_ctx| unsafe {
            let numeral_string = z3::get_numeral_string(*z3_ctx, ast);
            let numeral_str = std::ffi::CStr::from_ptr(numeral_string).to_str().unwrap();
            let sort = z3::get_sort(*z3_ctx, ast);
            let width = z3::get_bv_sort_size(*z3_ctx, sort);
            let value = BitVec::from_str(numeral_str, width).unwrap();
            value == expected_value
        })
    }

    fn verify_z3_symbol_name(ast: z3::Ast, expected_name: &str) -> bool {
        Z3_CONTEXT.with(|z3_ctx| unsafe {
            let ast_kind = z3::get_ast_kind(*z3_ctx, ast);
            if ast_kind != z3::AstKind::App {
                return false;
            }

            let app = z3::to_app(*z3_ctx, ast);
            let decl = z3::get_app_decl(*z3_ctx, app);
            let decl_kind = z3::get_decl_kind(*z3_ctx, decl);

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
        ast: &BitVecAst<'c>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        match ast.to_z3() {
            Ok(z3_ast) => BitVecAst::from_z3(ctx, z3_ast),
            Err(e) => Err(e),
        }
    }

    // One-way conversion tests (Clarirs -> Z3)
    mod to_z3 {
        use super::*;

        #[test]
        fn symbol() {
            let ctx = Context::new();
            let bv = ctx.bvs("x", 32).unwrap();
            let z3_ast = bv.to_z3().unwrap();

            // Verify it's an uninterpreted constant with correct name
            assert!(verify_z3_symbol_name(*z3_ast, "x"));

            // Get the sort and verify width
            Z3_CONTEXT.with(|z3_ctx| unsafe {
                let sort = z3::get_sort(*z3_ctx, *z3_ast);
                assert_eq!(z3::get_bv_sort_size(*z3_ctx, sort), 32);
            });
        }

        #[test]
        fn values() {
            let ctx = Context::new();

            // Test 8-bit value
            let bv8 = ctx.bvv_prim(42u8).unwrap();
            let z3_ast8 = bv8.to_z3().unwrap();
            assert!(verify_z3_ast_kind(*z3_ast8, z3::DeclKind::Bnum));
            assert!(verify_z3_bv_value(
                *z3_ast8,
                BitVec::from_prim(42u8).unwrap()
            ));

            // Test 32-bit value
            let bv32 = ctx.bvv_prim(0xDEADBEEFu32).unwrap();
            let z3_ast32 = bv32.to_z3().unwrap();
            assert!(verify_z3_ast_kind(*z3_ast32, z3::DeclKind::Bnum));
            assert!(verify_z3_bv_value(*z3_ast32, BitVec::from(0xDEADBEEFu32)));

            // Test 64-bit value
            let bv64 = ctx.bvv_prim(0x0123456789ABCDEFu64).unwrap();
            let z3_ast64 = bv64.to_z3().unwrap();
            assert!(verify_z3_ast_kind(*z3_ast64, z3::DeclKind::Bnum));
            assert!(verify_z3_bv_value(
                *z3_ast64,
                BitVec::from(0x0123456789ABCDEFu64)
            ));
        }

        #[test]
        fn not() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0xAAu8).unwrap(); // 10101010
            let not_bv = ctx.not(bv).unwrap();
            let z3_ast = not_bv.to_z3().unwrap();

            // Verify it's a NOT operation
            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Bnot));

            // Verify the operand
            let arg = get_z3_app_arg(*z3_ast, 0).unwrap();
            assert!(verify_z3_bv_value(arg, BitVec::from(0xAAu8)));
        }

        #[test]
        fn and() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(0xF0u8).unwrap(); // 11110000
            let bv2 = ctx.bvv_prim(0xAAu8).unwrap(); // 10101010
            let and_bv = ctx.and(bv1, bv2).unwrap();
            let z3_ast = and_bv.to_z3().unwrap();

            // Verify it's an AND operation
            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Band));

            // Verify the operands
            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(0xF0u8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(0xAAu8)));
        }

        #[test]
        fn or() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(0xF0u8).unwrap(); // 11110000
            let bv2 = ctx.bvv_prim(0x0Fu8).unwrap(); // 00001111
            let or_bv = ctx.or(bv1, bv2).unwrap();
            let z3_ast = or_bv.to_z3().unwrap();

            // Verify it's an OR operation
            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Bor));

            // Verify the operands
            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(0xF0u8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(0x0Fu8)));
        }

        #[test]
        fn xor() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(0xAAu8).unwrap(); // 10101010
            let bv2 = ctx.bvv_prim(0x55u8).unwrap(); // 01010101
            let xor_bv = ctx.xor(bv1, bv2).unwrap();
            let z3_ast = xor_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Bxor));

            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(0xAAu8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(0x55u8)));
        }

        #[test]
        fn add() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(42u8).unwrap();
            let bv2 = ctx.bvv_prim(13u8).unwrap();
            let add_bv = ctx.add(bv1, bv2).unwrap();
            let z3_ast = add_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Badd));

            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(42u8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(13u8)));
        }

        #[test]
        fn sub() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(42u8).unwrap();
            let bv2 = ctx.bvv_prim(13u8).unwrap();
            let sub_bv = ctx.sub(bv1, bv2).unwrap();
            let z3_ast = sub_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Bsub));

            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(42u8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(13u8)));
        }

        #[test]
        fn mul() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(6u8).unwrap();
            let bv2 = ctx.bvv_prim(7u8).unwrap();
            let mul_bv = ctx.mul(bv1, bv2).unwrap();
            let z3_ast = mul_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Bmul));

            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(6u8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(7u8)));
        }

        #[test]
        fn udiv() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(42u8).unwrap();
            let bv2 = ctx.bvv_prim(6u8).unwrap();
            let div_bv = ctx.udiv(bv1, bv2).unwrap();
            let z3_ast = div_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Budiv));

            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(42u8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(6u8)));
        }

        #[test]
        fn sdiv() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(-42i8 as u8).unwrap();
            let bv2 = ctx.bvv_prim(6u8).unwrap();
            let div_bv = ctx.sdiv(bv1, bv2).unwrap();
            let z3_ast = div_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Bsdiv));

            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(-42i8 as u8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(6u8)));
        }

        #[test]
        fn urem() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(42u8).unwrap();
            let bv2 = ctx.bvv_prim(5u8).unwrap();
            let rem_bv = ctx.urem(bv1, bv2).unwrap();
            let z3_ast = rem_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Burem));

            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(42u8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(5u8)));
        }

        #[test]
        fn srem() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(-42i8 as u8).unwrap();
            let bv2 = ctx.bvv_prim(5u8).unwrap();
            let rem_bv = ctx.srem(bv1, bv2).unwrap();
            let z3_ast = rem_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Bsrem));

            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(-42i8 as u8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(5u8)));
        }

        #[test]
        fn shl() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0x12u8).unwrap();
            let shift = ctx.bvv_prim(2u8).unwrap();
            let shl_bv = ctx.shl(bv, shift).unwrap();
            let z3_ast = shl_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Bshl));

            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(0x12u8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(2u8)));
        }

        #[test]
        fn lshr() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0x12u8).unwrap();
            let shift = ctx.bvv_prim(2u8).unwrap();
            let lshr_bv = ctx.lshr(bv, shift).unwrap();
            let z3_ast = lshr_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Blshr));

            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(0x12u8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(2u8)));
        }

        #[test]
        fn ashr() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0x82u8).unwrap(); // Negative number in two's complement
            let shift = ctx.bvv_prim(2u8).unwrap();
            let ashr_bv = ctx.ashr(bv, shift).unwrap();
            let z3_ast = ashr_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Bashr));

            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(0x82u8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(2u8)));
        }

        #[test]
        fn rotate_left() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0x12u8).unwrap();
            let rot = ctx.bvv_prim(2u8).unwrap();
            let rotl_bv = ctx.rotate_left(bv, rot).unwrap();
            let z3_ast = rotl_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::ExtRotateLeft));

            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(0x12u8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(2u8)));
        }

        #[test]
        fn rotate_right() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0x12u8).unwrap();
            let rot = ctx.bvv_prim(2u8).unwrap();
            let rotr_bv = ctx.rotate_right(bv, rot).unwrap();
            let z3_ast = rotr_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::ExtRotateRight));

            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(0x12u8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(2u8)));
        }

        #[test]
        fn zero_ext() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0x12u8).unwrap();
            let ext_bv = ctx.zero_ext(bv, 8).unwrap(); // Extend to 16 bits
            let z3_ast = ext_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::ZeroExt));

            let arg = get_z3_app_arg(*z3_ast, 0).unwrap();
            assert!(verify_z3_bv_value(arg, BitVec::from(0x12u8)));
        }

        #[test]
        fn sign_ext() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0x82u8).unwrap(); // Negative number in two's complement
            let ext_bv = ctx.sign_ext(bv, 8).unwrap(); // Extend to 16 bits
            let z3_ast = ext_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::SignExt));

            let arg = get_z3_app_arg(*z3_ast, 0).unwrap();
            assert!(verify_z3_bv_value(arg, BitVec::from(0x82u8)));
        }

        #[test]
        fn extract() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0xFFu8).unwrap();
            let ext_bv = ctx.extract(bv, 6, 2).unwrap(); // Extract bits [6:2]
            let z3_ast = ext_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Extract));

            let arg = get_z3_app_arg(*z3_ast, 0).unwrap();
            assert!(verify_z3_bv_value(arg, BitVec::from(0xFFu8)));
        }

        #[test]
        fn concat() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(0xAAu8).unwrap();
            let bv2 = ctx.bvv_prim(0xBBu8).unwrap();
            let concat_bv = ctx.concat(bv1, bv2).unwrap();
            let z3_ast = concat_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Concat));

            let arg0 = get_z3_app_arg(*z3_ast, 0).unwrap();
            let arg1 = get_z3_app_arg(*z3_ast, 1).unwrap();
            assert!(verify_z3_bv_value(arg0, BitVec::from(0xAAu8)));
            assert!(verify_z3_bv_value(arg1, BitVec::from(0xBBu8)));
        }

        #[test]
        fn if_() {
            let ctx = Context::new();
            let cond = ctx.true_().unwrap();
            let then_bv = ctx.bvv_prim(0xAAu8).unwrap();
            let else_bv = ctx.bvv_prim(0xBBu8).unwrap();
            let if_bv = ctx.ite(cond, then_bv, else_bv).unwrap();
            let z3_ast = if_bv.to_z3().unwrap();

            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::Ite));

            let then_arg = get_z3_app_arg(*z3_ast, 1).unwrap();
            let else_arg = get_z3_app_arg(*z3_ast, 2).unwrap();
            assert!(verify_z3_bv_value(then_arg, BitVec::from(0xAAu8)));
            assert!(verify_z3_bv_value(else_arg, BitVec::from(0xBBu8)));
        }
    }

    // One-way conversion tests (Z3 -> Clarirs)
    mod from_z3 {
        use super::*;

        #[test]
        fn symbol() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    // Create a Z3 bitvector symbol
                    let s_cstr = std::ffi::CString::new("x").unwrap();
                    let sym = z3::mk_string_symbol(*z3_ctx, s_cstr.as_ptr());
                    let sort = z3::mk_bv_sort(*z3_ctx, 32);
                    let decl = z3::mk_func_decl(*z3_ctx, sym, 0, std::ptr::null(), sort);
                    let z3_ast =
                        RcAst::try_from(z3::mk_app(*z3_ctx, decl, 0, std::ptr::null())).unwrap();

                    // Convert from Z3 to Clarirs
                    let result = BitVecAst::from_z3(&ctx, z3_ast).unwrap();
                    let expected = ctx.bvs("x", 32).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn values() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    // Test 8-bit value
                    let sort8 = z3::mk_bv_sort(*z3_ctx, 8);
                    let numeral8 = std::ffi::CString::new("42").unwrap();
                    let z3_ast8 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, numeral8.as_ptr(), sort8)).unwrap();

                    let result8 = BitVecAst::from_z3(&ctx, z3_ast8).unwrap();
                    let expected8 = ctx.bvv_prim(42u8).unwrap();
                    assert_eq!(result8, expected8);

                    // Test 32-bit value
                    let sort32 = z3::mk_bv_sort(*z3_ctx, 32);
                    let numeral32 = std::ffi::CString::new("3735928559").unwrap(); // 0xDEADBEEF
                    let z3_ast32 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, numeral32.as_ptr(), sort32))
                            .unwrap();

                    let result32 = BitVecAst::from_z3(&ctx, z3_ast32).unwrap();
                    let expected32 = ctx.bvv_prim(0xDEADBEEFu32).unwrap();
                    assert_eq!(result32, expected32);

                    // Test 64-bit value
                    let sort64 = z3::mk_bv_sort(*z3_ctx, 64);
                    let numeral64 = std::ffi::CString::new("81985529216486895").unwrap(); // 0x0123456789ABCDEF
                    let z3_ast64 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, numeral64.as_ptr(), sort64))
                            .unwrap();

                    let result64 = BitVecAst::from_z3(&ctx, z3_ast64).unwrap();
                    let expected64 = ctx.bvv_prim(0x0123456789ABCDEFu64).unwrap();
                    assert_eq!(result64, expected64);
                });
            }
        }

        #[test]
        fn not() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    // Create base value
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);
                    let numeral = std::ffi::CString::new("170").unwrap(); // 0xAA
                    let base =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, numeral.as_ptr(), sort)).unwrap();

                    // Create NOT operation
                    let not_z3 = RcAst::try_from(z3::mk_bvnot(*z3_ctx, *base)).unwrap();

                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, not_z3).unwrap();
                    let base_bv = ctx.bvv_prim(0xAAu8).unwrap();
                    let expected = ctx.not(base_bv).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn and() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("240").unwrap(); // 0xF0
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("170").unwrap(); // 0xAA
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create AND operation
                    let and_z3 = RcAst::try_from(z3::mk_bvand(*z3_ctx, *op1, *op2)).unwrap();

                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, and_z3).unwrap();
                    let bv1 = ctx.bvv_prim(0xF0u8).unwrap();
                    let bv2 = ctx.bvv_prim(0xAAu8).unwrap();
                    let expected = ctx.and(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn or() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("240").unwrap(); // 0xF0
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("15").unwrap(); // 0x0F
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create OR operation
                    let or_z3 = RcAst::try_from(z3::mk_bvor(*z3_ctx, *op1, *op2)).unwrap();
                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, or_z3).unwrap();
                    let bv1 = ctx.bvv_prim(0xF0u8).unwrap();
                    let bv2 = ctx.bvv_prim(0x0Fu8).unwrap();
                    let expected = ctx.or(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn xor() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("170").unwrap(); // 0xAA
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("85").unwrap(); // 0x55
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create XOR operation
                    let xor_z3 = RcAst::try_from(z3::mk_bvxor(*z3_ctx, *op1, *op2)).unwrap();

                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, xor_z3).unwrap();
                    let bv1 = ctx.bvv_prim(0xAAu8).unwrap();
                    let bv2 = ctx.bvv_prim(0x55u8).unwrap();
                    let expected = ctx.xor(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn add() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("42").unwrap();
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("13").unwrap();
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create ADD operation
                    let add_z3 = RcAst::try_from(z3::mk_bvadd(*z3_ctx, *op1, *op2)).unwrap();

                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, add_z3).unwrap();
                    let bv1 = ctx.bvv_prim(42u8).unwrap();
                    let bv2 = ctx.bvv_prim(13u8).unwrap();
                    let expected = ctx.add(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn sub() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("42").unwrap();
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("13").unwrap();
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create SUB operation
                    let sub_z3 = RcAst::try_from(z3::mk_bvsub(*z3_ctx, *op1, *op2)).unwrap();
                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, sub_z3).unwrap();
                    let bv1 = ctx.bvv_prim(42u8).unwrap();
                    let bv2 = ctx.bvv_prim(13u8).unwrap();
                    let expected = ctx.sub(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn mul() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("6").unwrap();
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("7").unwrap();
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create MUL operation
                    let mul_z3 = RcAst::try_from(z3::mk_bvmul(*z3_ctx, *op1, *op2)).unwrap();
                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, mul_z3).unwrap();
                    let bv1 = ctx.bvv_prim(6u8).unwrap();
                    let bv2 = ctx.bvv_prim(7u8).unwrap();
                    let expected = ctx.mul(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn udiv() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("42").unwrap();
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("6").unwrap();
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create UDIV operation
                    let udiv_z3 = RcAst::try_from(z3::mk_bvudiv(*z3_ctx, *op1, *op2)).unwrap();
                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, udiv_z3).unwrap();
                    let bv1 = ctx.bvv_prim(42u8).unwrap();
                    let bv2 = ctx.bvv_prim(6u8).unwrap();
                    let expected = ctx.udiv(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn sdiv() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("214").unwrap(); // -42 in two's complement
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("6").unwrap();
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create SDIV operation
                    let sdiv_z3 = RcAst::try_from(z3::mk_bvsdiv(*z3_ctx, *op1, *op2)).unwrap();

                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, sdiv_z3).unwrap();
                    let bv1 = ctx.bvv_prim(-42i8 as u8).unwrap();
                    let bv2 = ctx.bvv_prim(6u8).unwrap();
                    let expected = ctx.sdiv(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn urem() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("42").unwrap();
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("5").unwrap();
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create UREM operation
                    let urem_z3 = RcAst::try_from(z3::mk_bvurem(*z3_ctx, *op1, *op2)).unwrap();

                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, urem_z3).unwrap();
                    let bv1 = ctx.bvv_prim(42u8).unwrap();
                    let bv2 = ctx.bvv_prim(5u8).unwrap();
                    let expected = ctx.urem(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn srem() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("214").unwrap(); // -42 in two's complement
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("5").unwrap();
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create SREM operation
                    let srem_z3 = RcAst::try_from(z3::mk_bvsrem(*z3_ctx, *op1, *op2)).unwrap();

                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, srem_z3).unwrap();
                    let bv1 = ctx.bvv_prim(-42i8 as u8).unwrap();
                    let bv2 = ctx.bvv_prim(5u8).unwrap();
                    let expected = ctx.srem(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn shl() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("18").unwrap(); // 0x12
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("2").unwrap();
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create SHL operation
                    let shl_z3 = RcAst::try_from(z3::mk_bvshl(*z3_ctx, *op1, *op2)).unwrap();

                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, shl_z3).unwrap();
                    let bv1 = ctx.bvv_prim(0x12u8).unwrap();
                    let bv2 = ctx.bvv_prim(2u8).unwrap();
                    let expected = ctx.shl(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn lshr() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("18").unwrap(); // 0x12
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("2").unwrap();
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create LSHR operation
                    let lshr_z3 = RcAst::try_from(z3::mk_bvlshr(*z3_ctx, *op1, *op2)).unwrap();
                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, lshr_z3).unwrap();
                    let bv1 = ctx.bvv_prim(0x12u8).unwrap();
                    let bv2 = ctx.bvv_prim(2u8).unwrap();
                    let expected = ctx.lshr(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn ashr() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("130").unwrap(); // 0x82 (negative in two's complement)
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("2").unwrap();
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create ASHR operation
                    let ashr_z3 = RcAst::try_from(z3::mk_bvashr(*z3_ctx, *op1, *op2)).unwrap();

                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, ashr_z3).unwrap();
                    let bv1 = ctx.bvv_prim(0x82u8).unwrap();
                    let bv2 = ctx.bvv_prim(2u8).unwrap();
                    let expected = ctx.ashr(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn rotate_left() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("18").unwrap(); // 0x12
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("2").unwrap();
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create rotate left operation
                    let rotl_z3 =
                        RcAst::try_from(z3::mk_ext_rotate_left(*z3_ctx, *op1, *op2)).unwrap();

                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, rotl_z3).unwrap();
                    let bv1 = ctx.bvv_prim(0x12u8).unwrap();
                    let bv2 = ctx.bvv_prim(2u8).unwrap();
                    let expected = ctx.rotate_left(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn rotate_right() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("18").unwrap(); // 0x12
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("2").unwrap();
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create rotate right operation
                    let rotr_z3 =
                        RcAst::try_from(z3::mk_ext_rotate_right(*z3_ctx, *op1, *op2)).unwrap();
                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, rotr_z3).unwrap();
                    let bv1 = ctx.bvv_prim(0x12u8).unwrap();
                    let bv2 = ctx.bvv_prim(2u8).unwrap();
                    let expected = ctx.rotate_right(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn zero_ext() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create base value
                    let num = std::ffi::CString::new("18").unwrap(); // 0x12
                    let base =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num.as_ptr(), sort)).unwrap();

                    // Create zero extension (extend by 8 bits)
                    let zext_z3 = RcAst::try_from(z3::mk_zero_ext(*z3_ctx, 8, *base)).unwrap();

                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, zext_z3).unwrap();
                    let bv = ctx.bvv_prim(0x12u8).unwrap();
                    let expected = ctx.zero_ext(bv, 8).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn sign_ext() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create base value (negative number)
                    let num = std::ffi::CString::new("130").unwrap(); // 0x82 (negative in two's complement)
                    let base =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num.as_ptr(), sort)).unwrap();

                    // Create sign extension (extend by 8 bits)
                    let sext_z3 = RcAst::try_from(z3::mk_sign_ext(*z3_ctx, 8, *base)).unwrap();
                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, sext_z3).unwrap();
                    let bv = ctx.bvv_prim(0x82u8).unwrap();
                    let expected = ctx.sign_ext(bv, 8).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn extract() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create base value
                    let num = std::ffi::CString::new("255").unwrap(); // 0xFF
                    let base =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num.as_ptr(), sort)).unwrap();

                    // Create extract operation (bits [6:2])
                    let extract_z3 = RcAst::try_from(z3::mk_extract(*z3_ctx, 6, 2, *base)).unwrap();

                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, extract_z3).unwrap();
                    let bv = ctx.bvv_prim(0xFFu8).unwrap();
                    let expected = ctx.extract(bv, 6, 2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn concat() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create operands
                    let num1 = std::ffi::CString::new("170").unwrap(); // 0xAA
                    let op1 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("187").unwrap(); // 0xBB
                    let op2 =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create concatenation
                    let concat_z3 = RcAst::try_from(z3::mk_concat(*z3_ctx, *op1, *op2)).unwrap();
                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, concat_z3).unwrap();
                    let bv1 = ctx.bvv_prim(0xAAu8).unwrap();
                    let bv2 = ctx.bvv_prim(0xBBu8).unwrap();
                    let expected = ctx.concat(bv1, bv2).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn if_() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let sort = z3::mk_bv_sort(*z3_ctx, 8);

                    // Create condition (true)
                    let cond = RcAst::try_from(z3::mk_true(*z3_ctx)).unwrap();

                    // Create then and else values
                    let num1 = std::ffi::CString::new("170").unwrap(); // 0xAA
                    let then_val =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num1.as_ptr(), sort)).unwrap();

                    let num2 = std::ffi::CString::new("187").unwrap(); // 0xBB
                    let else_val =
                        RcAst::try_from(z3::mk_numeral(*z3_ctx, num2.as_ptr(), sort)).unwrap();

                    // Create if-then-else
                    let ite_z3 =
                        RcAst::try_from(z3::mk_ite(*z3_ctx, *cond, *then_val, *else_val)).unwrap();

                    // Convert and verify
                    let result = BitVecAst::from_z3(&ctx, ite_z3).unwrap();
                    let cond = ctx.true_().unwrap();
                    let then_bv = ctx.bvv_prim(0xAAu8).unwrap();
                    let else_bv = ctx.bvv_prim(0xBBu8).unwrap();
                    let expected = ctx.ite(cond, then_bv, else_bv).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }
    }

    // Round-trip conversion tests
    mod roundtrip {
        use super::*;

        #[test]
        fn symbol() {
            let ctx = Context::new();
            let bv = ctx.bvs("x", 32).unwrap();
            let result = round_trip(&ctx, &bv).unwrap();
            assert_eq!(bv, result);
        }

        #[test]
        fn values() {
            let ctx = Context::new();

            // Test 8-bit value
            let bv8 = ctx.bvv_prim(42u8).unwrap();
            let result8 = round_trip(&ctx, &bv8).unwrap();
            assert_eq!(bv8, result8);

            // Test 32-bit value
            let bv32 = ctx.bvv_prim(0xDEADBEEFu32).unwrap();
            let result32 = round_trip(&ctx, &bv32).unwrap();
            assert_eq!(bv32, result32);

            // Test 64-bit value
            let bv64 = ctx.bvv_prim(0x0123456789ABCDEFu64).unwrap();
            let result64 = round_trip(&ctx, &bv64).unwrap();
            assert_eq!(bv64, result64);
        }

        #[test]
        fn not() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0xAAu8).unwrap();
            let not_bv = ctx.not(bv).unwrap();
            let result = round_trip(&ctx, &not_bv).unwrap();
            assert_eq!(not_bv, result);
        }

        #[test]
        fn and() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(0xF0u8).unwrap();
            let bv2 = ctx.bvv_prim(0xAAu8).unwrap();
            let and_bv = ctx.and(bv1, bv2).unwrap();
            let result = round_trip(&ctx, &and_bv).unwrap();
            assert_eq!(and_bv, result);
        }

        #[test]
        fn or() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(0xF0u8).unwrap();
            let bv2 = ctx.bvv_prim(0x0Fu8).unwrap();
            let or_bv = ctx.or(bv1, bv2).unwrap();
            let result = round_trip(&ctx, &or_bv).unwrap();
            assert_eq!(or_bv, result);
        }

        #[test]
        fn xor() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(0xAAu8).unwrap();
            let bv2 = ctx.bvv_prim(0x55u8).unwrap();
            let xor_bv = ctx.xor(bv1, bv2).unwrap();
            let result = round_trip(&ctx, &xor_bv).unwrap();
            assert_eq!(xor_bv, result);
        }

        #[test]
        fn add() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(42u8).unwrap();
            let bv2 = ctx.bvv_prim(13u8).unwrap();
            let add_bv = ctx.add(bv1, bv2).unwrap();
            let result = round_trip(&ctx, &add_bv).unwrap();
            assert_eq!(add_bv, result);
        }

        #[test]
        fn sub() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(42u8).unwrap();
            let bv2 = ctx.bvv_prim(13u8).unwrap();
            let sub_bv = ctx.sub(bv1, bv2).unwrap();
            let result = round_trip(&ctx, &sub_bv).unwrap();
            assert_eq!(sub_bv, result);
        }

        #[test]
        fn mul() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(6u8).unwrap();
            let bv2 = ctx.bvv_prim(7u8).unwrap();
            let mul_bv = ctx.mul(bv1, bv2).unwrap();
            let result = round_trip(&ctx, &mul_bv).unwrap();
            assert_eq!(mul_bv, result);
        }

        #[test]
        fn udiv() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(42u8).unwrap();
            let bv2 = ctx.bvv_prim(6u8).unwrap();
            let div_bv = ctx.udiv(bv1, bv2).unwrap();
            let result = round_trip(&ctx, &div_bv).unwrap();
            assert_eq!(div_bv, result);
        }

        #[test]
        fn sdiv() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(-42i8 as u8).unwrap();
            let bv2 = ctx.bvv_prim(6u8).unwrap();
            let div_bv = ctx.sdiv(bv1, bv2).unwrap();
            let result = round_trip(&ctx, &div_bv).unwrap();
            assert_eq!(div_bv, result);
        }

        #[test]
        fn urem() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(42u8).unwrap();
            let bv2 = ctx.bvv_prim(5u8).unwrap();
            let rem_bv = ctx.urem(bv1, bv2).unwrap();
            let result = round_trip(&ctx, &rem_bv).unwrap();
            assert_eq!(rem_bv, result);
        }

        #[test]
        fn srem() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(-42i8 as u8).unwrap();
            let bv2 = ctx.bvv_prim(5u8).unwrap();
            let rem_bv = ctx.srem(bv1, bv2).unwrap();
            let result = round_trip(&ctx, &rem_bv).unwrap();
            assert_eq!(rem_bv, result);
        }

        #[test]
        fn shl() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0x12u8).unwrap();
            let shift = ctx.bvv_prim(2u8).unwrap();
            let shl_bv = ctx.shl(bv, shift).unwrap();
            let result = round_trip(&ctx, &shl_bv).unwrap();
            assert_eq!(shl_bv, result);
        }

        #[test]
        fn lshr() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0x12u8).unwrap();
            let shift = ctx.bvv_prim(2u8).unwrap();
            let lshr_bv = ctx.lshr(bv, shift).unwrap();
            let result = round_trip(&ctx, &lshr_bv).unwrap();
            assert_eq!(lshr_bv, result);
        }

        #[test]
        fn ashr() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0x82u8).unwrap();
            let shift = ctx.bvv_prim(2u8).unwrap();
            let ashr_bv = ctx.ashr(bv, shift).unwrap();
            let result = round_trip(&ctx, &ashr_bv).unwrap();
            assert_eq!(ashr_bv, result);
        }

        #[test]
        fn rotate_left() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0x12u8).unwrap();
            let rot = ctx.bvv_prim(2u8).unwrap();
            let rotl_bv = ctx.rotate_left(bv, rot).unwrap();
            let result = round_trip(&ctx, &rotl_bv).unwrap();
            assert_eq!(rotl_bv, result);
        }

        #[test]
        fn rotate_right() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0x12u8).unwrap();
            let rot = ctx.bvv_prim(2u8).unwrap();
            let rotr_bv = ctx.rotate_right(bv, rot).unwrap();
            let result = round_trip(&ctx, &rotr_bv).unwrap();
            assert_eq!(rotr_bv, result);
        }

        #[test]
        fn zero_ext() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0x12u8).unwrap();
            let ext_bv = ctx.zero_ext(bv, 8).unwrap();
            let result = round_trip(&ctx, &ext_bv).unwrap();
            assert_eq!(ext_bv, result);
        }

        #[test]
        fn sign_ext() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0x82u8).unwrap();
            let ext_bv = ctx.sign_ext(bv, 8).unwrap();
            let result = round_trip(&ctx, &ext_bv).unwrap();
            assert_eq!(ext_bv, result);
        }

        #[test]
        fn extract() {
            let ctx = Context::new();
            let bv = ctx.bvv_prim(0xFFu8).unwrap();
            let ext_bv = ctx.extract(bv, 6, 2).unwrap();
            let result = round_trip(&ctx, &ext_bv).unwrap();
            assert_eq!(ext_bv, result);
        }

        #[test]
        fn concat() {
            let ctx = Context::new();
            let bv1 = ctx.bvv_prim(0xAAu8).unwrap();
            let bv2 = ctx.bvv_prim(0xBBu8).unwrap();
            let concat_bv = ctx.concat(bv1, bv2).unwrap();
            let result = round_trip(&ctx, &concat_bv).unwrap();
            assert_eq!(concat_bv, result);
        }

        #[test]
        fn if_() {
            let ctx = Context::new();
            let cond = ctx.true_().unwrap();
            let then_bv = ctx.bvv_prim(0xAAu8).unwrap();
            let else_bv = ctx.bvv_prim(0xBBu8).unwrap();
            let if_bv = ctx.ite(cond, then_bv, else_bv).unwrap();
            let result = round_trip(&ctx, &if_bv).unwrap();
            assert_eq!(if_bv, result);
        }

        #[test]
        fn fp_to_ieeebv() {
            let ctx = Context::new();
            let fp = ctx.fps("x", FSort::f32()).unwrap();
            let ieee_bv = ctx.fp_to_ieeebv(fp).unwrap();

            // Should convert to Z3 without panicking
            let z3_ast = ieee_bv.to_z3();
            assert!(z3_ast.is_ok());
        }

        #[test]
        fn fp_to_ubv() {
            let ctx = Context::new();
            let fp = ctx.fps("y", FSort::f32()).unwrap();
            let ubv = ctx.fp_to_ubv(fp, 32, FPRM::TowardZero).unwrap();

            // Should convert to Z3 without panicking
            let z3_ast = ubv.to_z3();
            assert!(z3_ast.is_ok());
        }

        #[test]
        fn fp_to_sbv() {
            let ctx = Context::new();
            let fp = ctx.fps("z", FSort::f32()).unwrap();
            let sbv = ctx.fp_to_sbv(fp, 32, FPRM::TowardZero).unwrap();

            // Should convert to Z3 without panicking
            let z3_ast = sbv.to_z3();
            assert!(z3_ast.is_ok());
        }
    }
}
