use crate::{Z3_CONTEXT, rc::RcAst};
use clarirs_core::prelude::*;
use clarirs_z3_sys::{self as z3};
use regex::Regex;

use super::AstExtZ3;

fn mk_bv2int(bv: RcAst) -> RcAst {
    Z3_CONTEXT.with(|&z3_ctx| unsafe { RcAst::from(z3::mk_bv2int(z3_ctx, bv.0, false)) })
}

fn decode_custom_unicode(input: &str) -> String {
    // Compile the regex pattern that matches "\u{...}"
    let re = Regex::new(r"\\u\{([0-9a-fA-F]+)\}").unwrap();

    // Replace all matches with the corresponding Unicode character.
    re.replace_all(input, |caps: &regex::Captures| {
        // Extract the hexadecimal part from the capture group.
        let num = u32::from_str_radix(&caps[1], 16).unwrap();
        // Convert the number to a Unicode character and then to a String.
        std::char::from_u32(num).unwrap().to_string()
    })
    .into_owned()
}

impl<'c> AstExtZ3<'c> for StringAst<'c> {
    fn to_z3(&self) -> Result<RcAst, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            Ok(match self.op() {
                StringOp::StringS(s) => {
                    let s_cstr = std::ffi::CString::new(s.as_str()).unwrap();
                    let sym = z3::mk_string_symbol(z3_ctx, s_cstr.as_ptr());
                    let sort = z3::mk_seq_sort(z3_ctx, z3::mk_char_sort(z3_ctx));
                    RcAst::from(z3::mk_const(z3_ctx, sym, sort))
                }
                StringOp::StringV(s) => {
                    let mut encoded = String::new();
                    for ch in s.chars() {
                        if ch.is_ascii() {
                            encoded.push(ch);
                        } else {
                            let escape = format!("\\u{{{:04X}}}", ch as u32);
                            encoded.push_str(&escape);
                        }
                    }
                    let cstr = std::ffi::CString::new(encoded).unwrap();
                    RcAst::from(z3::mk_string(z3_ctx, cstr.as_ptr()))
                }
                StringOp::StrConcat(a, b) => {
                    let a = a.to_z3()?;
                    let b = b.to_z3()?;
                    let args = [a.0, b.0];
                    z3::mk_seq_concat(z3_ctx, 2, args.as_ptr()).into()
                }
                StringOp::StrSubstr(a, offset, len) => {
                    let a = a.to_z3()?;
                    let offset_bv = offset.to_z3()?;
                    let offset_int = mk_bv2int(offset_bv);
                    let len_bv = len.to_z3()?;
                    let len_int = mk_bv2int(len_bv);
                    z3::mk_seq_extract(z3_ctx, a.0, offset_int.0, len_int.0).into()
                }
                StringOp::StrReplace(a, b, c) => {
                    let a = a.to_z3()?;
                    let b = b.to_z3()?;
                    let c = c.to_z3()?;
                    z3::mk_seq_replace(z3_ctx, a.0, b.0, c.0).into()
                }
                StringOp::BVToStr(_) => todo!("BVToStr - no direct Z3 equivalent"),
                StringOp::If(cond, then, else_) => {
                    let cond = cond.to_z3()?;
                    let then = then.to_z3()?;
                    let else_ = else_.to_z3()?;
                    z3::mk_ite(z3_ctx, cond.0, then.0, else_.0).into()
                }
                StringOp::Annotated(inner, _) => inner.to_z3()?,
            })
            .and_then(|ast| {
                if ast.is_null() {
                    Err(ClarirsError::ConversionError(
                        "failed to create Z3 AST, got null".to_string(),
                    ))
                } else {
                    Ok(ast)
                }
            })
        })
    }

    fn from_z3(ctx: &'c Context<'c>, ast: impl Into<RcAst>) -> Result<Self, ClarirsError> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let ast = ast.into();
            let ast_kind = z3::get_ast_kind(z3_ctx, *ast);
            match ast_kind {
                z3::AstKind::App => {
                    let app = z3::to_app(z3_ctx, *ast);
                    let decl = z3::get_app_decl(z3_ctx, app);
                    let decl_kind = z3::get_decl_kind(z3_ctx, decl);

                    match decl_kind {
                        // Handle string constants
                        _ if z3::is_string(z3_ctx, *ast) => {
                            let string_ptr = z3::get_string(z3_ctx, *ast);
                            let raw_str = std::ffi::CStr::from_ptr(string_ptr).to_str().unwrap();
                            let decoded_str = decode_custom_unicode(raw_str);
                            ctx.stringv(decoded_str)
                        }
                        z3::DeclKind::Uninterpreted => {
                            // Verify it's a string
                            let sort = z3::get_sort(z3_ctx, *ast);
                            let sort_kind = z3::get_sort_kind(z3_ctx, sort);
                            if sort_kind != z3::SortKind::Seq {
                                return Err(ClarirsError::ConversionError(
                                    "expected a string".to_string(),
                                ));
                            }
                            let sym = z3::get_decl_name(z3_ctx, decl);
                            let name = z3::get_symbol_string(z3_ctx, sym);
                            let name = std::ffi::CStr::from_ptr(name).to_str().unwrap();
                            ctx.strings(name)
                        }
                        z3::DeclKind::SeqConcat => {
                            let arg0 = z3::get_app_arg(z3_ctx, app, 0);
                            let arg1 = z3::get_app_arg(z3_ctx, app, 1);
                            let a = StringAst::from_z3(ctx, arg0)?;
                            let b = StringAst::from_z3(ctx, arg1)?;
                            ctx.strconcat(&a, &b)
                        }
                        z3::DeclKind::SeqExtract => {
                            let arg0 = z3::get_app_arg(z3_ctx, app, 0);
                            let arg1 = z3::get_app_arg(z3_ctx, app, 1);
                            let arg2 = z3::get_app_arg(z3_ctx, app, 2);
                            let a = StringAst::from_z3(ctx, arg0)?;

                            let offset_bv = RcAst::from(z3::mk_int2bv(z3_ctx, 64, arg1));
                            let offset_simplified = RcAst::from(z3::simplify(z3_ctx, offset_bv.0));
                            let offset = BitVecAst::from_z3(ctx, offset_simplified)?;

                            let len_bv = RcAst::from(z3::mk_int2bv(z3_ctx, 64, arg2));
                            let len_simplified = RcAst::from(z3::simplify(z3_ctx, len_bv.0));
                            let len = BitVecAst::from_z3(ctx, len_simplified)?;

                            ctx.strsubstr(&a, &offset, &len)
                        }
                        z3::DeclKind::SeqReplace => {
                            let arg0 = z3::get_app_arg(z3_ctx, app, 0);
                            let arg1 = z3::get_app_arg(z3_ctx, app, 1);
                            let arg2 = z3::get_app_arg(z3_ctx, app, 2);
                            let a = StringAst::from_z3(ctx, arg0)?;
                            let b = StringAst::from_z3(ctx, arg1)?;
                            let c = StringAst::from_z3(ctx, arg2)?;
                            ctx.strreplace(&a, &b, &c)
                        }
                        z3::DeclKind::Ite => {
                            let cond = z3::get_app_arg(z3_ctx, app, 0);
                            let then = z3::get_app_arg(z3_ctx, app, 1);
                            let else_ = z3::get_app_arg(z3_ctx, app, 2);
                            let cond = BoolAst::from_z3(ctx, cond)?;
                            let then = StringAst::from_z3(ctx, then)?;
                            let else_ = StringAst::from_z3(ctx, else_)?;
                            ctx.if_(&cond, &then, &else_)
                        }
                        _ => Err(ClarirsError::ConversionError(
                            "unsupported operation".to_string(),
                        )),
                    }
                }
                _ => Err(ClarirsError::ConversionError(
                    "unsupported operation".to_string(),
                )),
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Helper functions to verify Z3 AST structure and values
    fn verify_z3_ast_kind(ast: z3::Ast, expected_kind: z3::DeclKind) -> bool {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let app = z3::to_app(z3_ctx, ast);
            let decl = z3::get_app_decl(z3_ctx, app);
            let kind = z3::get_decl_kind(z3_ctx, decl);
            kind == expected_kind
        })
    }

    fn verify_z3_string_value(ast: z3::Ast, expected_value: &str) -> bool {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let string_ptr = z3::get_string(z3_ctx, ast);
            if string_ptr.is_null() {
                return false;
            }
            let string = std::ffi::CStr::from_ptr(string_ptr).to_str().unwrap();
            string == expected_value
        })
    }

    fn verify_z3_symbol_name(ast: z3::Ast, expected_name: &str) -> bool {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let ast_kind = z3::get_ast_kind(z3_ctx, ast);
            if ast_kind != z3::AstKind::App {
                return false;
            }

            let app = z3::to_app(z3_ctx, ast);
            let decl = z3::get_app_decl(z3_ctx, app);
            let decl_kind = z3::get_decl_kind(z3_ctx, decl);

            if decl_kind != z3::DeclKind::Uninterpreted {
                return false;
            }

            let sym = z3::get_decl_name(z3_ctx, decl);
            let name = z3::get_symbol_string(z3_ctx, sym);
            let name = std::ffi::CStr::from_ptr(name).to_str().unwrap();
            name == expected_name
        })
    }

    fn get_z3_app_arg(ast: z3::Ast, index: u32) -> Option<z3::Ast> {
        Z3_CONTEXT.with(|&z3_ctx| unsafe {
            let ast_kind = z3::get_ast_kind(z3_ctx, ast);
            if ast_kind != z3::AstKind::App {
                return None;
            }

            let app = z3::to_app(z3_ctx, ast);
            let num_args = z3::get_app_num_args(z3_ctx, app);
            if index >= num_args {
                return None;
            }

            Some(z3::get_app_arg(z3_ctx, app, index))
        })
    }

    fn round_trip<'c>(
        ctx: &'c Context<'c>,
        ast: &StringAst<'c>,
    ) -> Result<StringAst<'c>, ClarirsError> {
        StringAst::from_z3(ctx, ast.to_z3()?)
    }

    // One-way conversion tests
    mod to_z3 {
        use super::*;

        #[test]
        fn symbol() {
            let ctx = Context::new();
            let sym = ctx.strings("x").unwrap();

            let z3_ast = sym.to_z3().unwrap();
            assert!(verify_z3_symbol_name(*z3_ast, "x"));
        }

        #[test]
        fn values() {
            let ctx = Context::new();
            let val = ctx.stringv("hello").unwrap();

            let z3_ast = val.to_z3().unwrap();
            Z3_CONTEXT.with(|z3_ctx| unsafe {
                assert!(z3::is_string(*z3_ctx, *z3_ast));
            });
            assert!(verify_z3_string_value(*z3_ast, "hello"));
        }

        #[test]
        fn concat() {
            let ctx = Context::new();
            let s1 = ctx.stringv("hello").unwrap();
            let s2 = ctx.stringv(" world").unwrap();
            let concat = ctx.strconcat(&s1, &s2).unwrap();

            let z3_ast = concat.to_z3().unwrap();
            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::SeqConcat));

            // Verify operands
            let arg0 = get_z3_app_arg(*z3_ast, 0).expect("Failed to get first concat argument");
            let arg1 = get_z3_app_arg(*z3_ast, 1).expect("Failed to get second concat argument");
            assert!(verify_z3_string_value(arg0, "hello"));
            assert!(verify_z3_string_value(arg1, " world"));
        }

        #[test]
        fn substr() {
            let ctx = Context::new();
            let s = ctx.stringv("hello world").unwrap();
            let start = ctx.bvv_prim(6u32).unwrap();
            let length = ctx.bvv_prim(5u32).unwrap();
            let substr = ctx.strsubstr(&s, &start, &length).unwrap();

            let z3_ast = substr.to_z3().unwrap();
            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::SeqExtract));

            // Verify operands
            let arg0 = get_z3_app_arg(*z3_ast, 0).expect("Failed to get string argument");
            assert!(verify_z3_string_value(arg0, "hello world"));
        }

        #[test]
        fn replace() {
            let ctx = Context::new();
            let s = ctx.stringv("hello world").unwrap();
            let pattern = ctx.stringv("world").unwrap();
            let replacement = ctx.stringv("there").unwrap();
            let replaced = ctx.strreplace(&s, &pattern, &replacement).unwrap();

            let z3_ast = replaced.to_z3().unwrap();
            assert!(verify_z3_ast_kind(*z3_ast, z3::DeclKind::SeqReplace));

            // Verify operands
            let arg0 = get_z3_app_arg(*z3_ast, 0).expect("Failed to get string argument");
            let arg1 = get_z3_app_arg(*z3_ast, 1).expect("Failed to get pattern argument");
            let arg2 = get_z3_app_arg(*z3_ast, 2).expect("Failed to get replacement argument");
            assert!(verify_z3_string_value(arg0, "hello world"));
            assert!(verify_z3_string_value(arg1, "world"));
            assert!(verify_z3_string_value(arg2, "there"));
        }

        #[test]
        fn if_() {
            let ctx = Context::new();
            let cond = ctx.bools("c").unwrap();
            let then = ctx.stringv("then").unwrap();
            let else_ = ctx.stringv("else").unwrap();
            let if_expr = ctx.if_(&cond, &then, &else_).unwrap();

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
                verify_z3_string_value(then_ast, "then"),
                "IF then branch should be 'then'"
            );
            assert!(
                verify_z3_string_value(else_ast, "else"),
                "IF else branch should be 'else'"
            );
        }
    }

    // Tests for convert_string_from_z3
    mod from_z3 {
        use super::*;

        #[test]
        fn symbol() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    // Create a Z3 string symbol
                    let s_cstr = std::ffi::CString::new("x").unwrap();
                    let sym = z3::mk_string_symbol(*z3_ctx, s_cstr.as_ptr());
                    let sort = z3::mk_seq_sort(*z3_ctx, z3::mk_char_sort(*z3_ctx));
                    let decl = z3::mk_func_decl(*z3_ctx, sym, 0, std::ptr::null(), sort);
                    let z3_ast = z3::mk_app(*z3_ctx, decl, 0, std::ptr::null());

                    // Convert from Z3 to Clarirs
                    let result = StringAst::from_z3(&ctx, z3_ast).unwrap();
                    let expected = ctx.strings("x").unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn values() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    let s_cstr = std::ffi::CString::new("hello").unwrap();
                    let z3_ast = z3::mk_string(*z3_ctx, s_cstr.as_ptr());

                    let result = StringAst::from_z3(&ctx, z3_ast).unwrap();
                    let expected = ctx.stringv("hello").unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn concat() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    // Create string constants
                    let s1_cstr = std::ffi::CString::new("hello").unwrap();
                    let s1 = z3::mk_string(*z3_ctx, s1_cstr.as_ptr());
                    z3::inc_ref(*z3_ctx, s1);

                    let s2_cstr = std::ffi::CString::new(" world").unwrap();
                    let s2 = z3::mk_string(*z3_ctx, s2_cstr.as_ptr());
                    z3::inc_ref(*z3_ctx, s2);

                    // Create concatenation
                    let args = [s1, s2];
                    let concat = z3::mk_seq_concat(*z3_ctx, 2, args.as_ptr());
                    z3::inc_ref(*z3_ctx, concat);

                    // Convert and verify
                    let result = StringAst::from_z3(&ctx, concat).unwrap();
                    let s1_ast = ctx.stringv("hello").unwrap();
                    let s2_ast = ctx.stringv(" world").unwrap();
                    let expected = ctx.strconcat(&s1_ast, &s2_ast).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn substr() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    // Create string constant
                    let s_cstr = std::ffi::CString::new("hello world").unwrap();
                    let s = z3::mk_string(*z3_ctx, s_cstr.as_ptr());
                    z3::inc_ref(*z3_ctx, s);

                    // Create bitvector constants for start and length
                    let int_sort = z3::mk_int_sort(*z3_ctx);
                    let start_cstr = std::ffi::CString::new("6").unwrap();
                    let start = z3::mk_numeral(*z3_ctx, start_cstr.as_ptr(), int_sort);
                    z3::inc_ref(*z3_ctx, start);

                    let len_cstr = std::ffi::CString::new("5").unwrap();
                    let len = z3::mk_numeral(*z3_ctx, len_cstr.as_ptr(), int_sort);
                    z3::inc_ref(*z3_ctx, len);

                    // Create substring operation
                    let substr = z3::mk_seq_extract(*z3_ctx, s, start, len);
                    z3::inc_ref(*z3_ctx, substr);

                    // Convert and verify
                    let result = StringAst::from_z3(&ctx, substr).unwrap();
                    let s_ast = ctx.stringv("hello world").unwrap();
                    let start_ast = ctx.bvv_prim(6u64).unwrap();
                    let len_ast = ctx.bvv_prim(5u64).unwrap();
                    let expected = ctx.strsubstr(&s_ast, &start_ast, &len_ast).unwrap();
                    assert_eq!(result, expected);
                });
            }
        }

        #[test]
        fn replace() {
            unsafe {
                let ctx = Context::new();
                Z3_CONTEXT.with(|z3_ctx| {
                    // Create string constants
                    let s_cstr = std::ffi::CString::new("hello world").unwrap();
                    let s = z3::mk_string(*z3_ctx, s_cstr.as_ptr());
                    z3::inc_ref(*z3_ctx, s);

                    let pattern_cstr = std::ffi::CString::new("world").unwrap();
                    let pattern = z3::mk_string(*z3_ctx, pattern_cstr.as_ptr());
                    z3::inc_ref(*z3_ctx, pattern);

                    let replacement_cstr = std::ffi::CString::new("there").unwrap();
                    let replacement = z3::mk_string(*z3_ctx, replacement_cstr.as_ptr());
                    z3::inc_ref(*z3_ctx, replacement);

                    // Create replace operation
                    let replace = z3::mk_seq_replace(*z3_ctx, s, pattern, replacement);
                    z3::inc_ref(*z3_ctx, replace);

                    // Convert and verify
                    let result = StringAst::from_z3(&ctx, replace).unwrap();
                    let s_ast = ctx.stringv("hello world").unwrap();
                    let pattern_ast = ctx.stringv("world").unwrap();
                    let replacement_ast = ctx.stringv("there").unwrap();
                    let expected = ctx
                        .strreplace(&s_ast, &pattern_ast, &replacement_ast)
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
                    // Create condition (boolean symbol)
                    let c_cstr = std::ffi::CString::new("c").unwrap();
                    let c_sym = z3::mk_string_symbol(*z3_ctx, c_cstr.as_ptr());
                    let bool_sort = z3::mk_bool_sort(*z3_ctx);
                    let c_decl = z3::mk_func_decl(*z3_ctx, c_sym, 0, std::ptr::null(), bool_sort);
                    let cond = z3::mk_app(*z3_ctx, c_decl, 0, std::ptr::null());
                    z3::inc_ref(*z3_ctx, cond);

                    // Create string constants for then and else branches
                    let then_cstr = std::ffi::CString::new("then").unwrap();
                    let then_val = z3::mk_string(*z3_ctx, then_cstr.as_ptr());
                    z3::inc_ref(*z3_ctx, then_val);

                    let else_cstr = std::ffi::CString::new("else").unwrap();
                    let else_val = z3::mk_string(*z3_ctx, else_cstr.as_ptr());
                    z3::inc_ref(*z3_ctx, else_val);

                    // Create if-then-else
                    let ite = z3::mk_ite(*z3_ctx, cond, then_val, else_val);
                    z3::inc_ref(*z3_ctx, ite);

                    // Convert and verify
                    let result = StringAst::from_z3(&ctx, ite).unwrap();
                    let cond_ast = ctx.bools("c").unwrap();
                    let then_ast = ctx.stringv("then").unwrap();
                    let else_ast = ctx.stringv("else").unwrap();
                    let expected = ctx.if_(&cond_ast, &then_ast, &else_ast).unwrap();
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
            let sym = ctx.strings("x").unwrap();
            let result = round_trip(&ctx, &sym).unwrap();
            assert_eq!(sym, result);
        }

        #[test]
        fn values() {
            let ctx = Context::new();
            let val = ctx.stringv("hello").unwrap();
            let result = round_trip(&ctx, &val).unwrap();
            assert_eq!(val, result);
        }

        #[test]
        fn concat() {
            let ctx = Context::new();
            let s1 = ctx.stringv("hello").unwrap();
            let s2 = ctx.stringv(" world").unwrap();
            let concat = ctx.strconcat(&s1, &s2).unwrap();
            let result = round_trip(&ctx, &concat).unwrap();
            assert_eq!(concat, result);
        }

        #[test]
        fn substr() {
            let ctx = Context::new();
            let s = ctx.stringv("hello world").unwrap();
            let start = ctx.bvv_prim(6u64).unwrap();
            let length = ctx.bvv_prim(5u64).unwrap();
            let substr = ctx.strsubstr(&s, &start, &length).unwrap();
            let result = round_trip(&ctx, &substr).unwrap();
            assert_eq!(substr, result);
        }

        #[test]
        fn replace() {
            let ctx = Context::new();
            let s = ctx.stringv("hello world").unwrap();
            let pattern = ctx.stringv("world").unwrap();
            let replacement = ctx.stringv("there").unwrap();
            let replaced = ctx.strreplace(&s, &pattern, &replacement).unwrap();
            let result = round_trip(&ctx, &replaced).unwrap();
            assert_eq!(replaced, result);
        }

        #[test]
        fn if_() {
            let ctx = Context::new();
            let cond = ctx.bools("c").unwrap();
            let then = ctx.stringv("then").unwrap();
            let else_ = ctx.stringv("else").unwrap();
            let if_expr = ctx.if_(&cond, &then, &else_).unwrap();
            let result = round_trip(&ctx, &if_expr).unwrap();
            assert_eq!(if_expr, result);
        }
    }
}
