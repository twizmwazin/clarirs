use clarirs_core::prelude::*;
use z3::ast::{Ast, Dynamic, Bool, Int};

use super::AstExtZ3;

fn round_trip<'c>(
    ctx: &'c Context<'c>,
    ast: &StringAst<'c>,
) -> Result<StringAst<'c>, ClarirsError> {
    StringAst::from_z3(ctx, ast.to_z3()?)
}

/// Helper: check that a Z3 AST is a string with the given value.
fn assert_z3_string_value(ast: &Dynamic, expected: &str) {
    let s = ast.as_string().expect("expected a z3 string");
    let got = s.as_string().expect("expected a string constant");
    assert_eq!(got, expected);
}

// ---------------------------------------------------------------
// to_z3 tests
// ---------------------------------------------------------------
mod to_z3 {
    use super::*;

    // -- Leaf nodes --

    #[test]
    fn symbol() {
        let ctx = Context::new();
        let s = ctx.strings("x").unwrap();
        let z3_ast = s.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::UNINTERPRETED);
        assert_eq!(z3_ast.safe_decl().unwrap().name(), "x");
    }

    #[test]
    fn value_simple() {
        let ctx = Context::new();
        let s = ctx.stringv("hello").unwrap();
        let z3_ast = s.to_z3().unwrap();

        assert!(z3_ast.as_string().is_some());
        assert_z3_string_value(&z3_ast, "hello");
    }

    #[test]
    fn value_empty() {
        let ctx = Context::new();
        let s = ctx.stringv("").unwrap();
        let z3_ast = s.to_z3().unwrap();

        assert!(z3_ast.as_string().is_some());
        assert_z3_string_value(&z3_ast, "");
    }

    #[test]
    fn value_with_spaces() {
        let ctx = Context::new();
        let s = ctx.stringv("hello world").unwrap();
        let z3_ast = s.to_z3().unwrap();
        assert_z3_string_value(&z3_ast, "hello world");
    }

    // -- StrConcat --

    #[test]
    fn concat() {
        let ctx = Context::new();
        let s1 = ctx.stringv("hello").unwrap();
        let s2 = ctx.stringv(" world").unwrap();
        let cat = ctx.str_concat(s1, s2).unwrap();
        let z3_ast = cat.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::SEQ_CONCAT);
        assert_eq!(z3_ast.num_children() as u32, 2);
        assert_z3_string_value(&z3_ast.nth_child(0).unwrap(), "hello");
        assert_z3_string_value(&z3_ast.nth_child(1).unwrap(), " world");
    }

    #[test]
    fn concat_symbols() {
        let ctx = Context::new();
        let s1 = ctx.strings("a").unwrap();
        let s2 = ctx.strings("b").unwrap();
        let cat = ctx.str_concat(s1, s2).unwrap();
        let z3_ast = cat.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::SEQ_CONCAT);
        assert_eq!(z3_ast.num_children() as u32, 2);
        assert_eq!(z3_ast.nth_child(0).unwrap().safe_decl().unwrap().name(), "a");
        assert_eq!(z3_ast.nth_child(1).unwrap().safe_decl().unwrap().name(), "b");
    }

    // -- StrSubstr --

    #[test]
    fn substr() {
        let ctx = Context::new();
        let s = ctx.stringv("hello world").unwrap();
        let start = ctx.bvv_prim(6u32).unwrap();
        let length = ctx.bvv_prim(5u32).unwrap();
        let sub = ctx.str_substr(s, start, length).unwrap();
        let z3_ast = sub.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::SEQ_EXTRACT);
        assert_eq!(z3_ast.num_children() as u32, 3);
        assert_z3_string_value(&z3_ast.nth_child(0).unwrap(), "hello world");
    }

    // -- StrReplace --

    #[test]
    fn replace() {
        let ctx = Context::new();
        let s = ctx.stringv("hello world").unwrap();
        let pat = ctx.stringv("world").unwrap();
        let rep = ctx.stringv("there").unwrap();
        let replaced = ctx.str_replace(s, pat, rep).unwrap();
        let z3_ast = replaced.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::SEQ_REPLACE);
        assert_eq!(z3_ast.num_children() as u32, 3);
        assert_z3_string_value(&z3_ast.nth_child(0).unwrap(), "hello world");
        assert_z3_string_value(&z3_ast.nth_child(1).unwrap(), "world");
        assert_z3_string_value(&z3_ast.nth_child(2).unwrap(), "there");
    }

    // -- ITE --

    #[test]
    fn ite() {
        let ctx = Context::new();
        let c = ctx.bools("c").unwrap();
        let then = ctx.stringv("then").unwrap();
        let else_ = ctx.stringv("else").unwrap();
        let ite = ctx.ite(c, then, else_).unwrap();
        let z3_ast = ite.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::ITE);
        assert_eq!(z3_ast.num_children() as u32, 3);
        assert_eq!(z3_ast.nth_child(0).unwrap().safe_decl().unwrap().name(), "c");
        assert_z3_string_value(&z3_ast.nth_child(1).unwrap(), "then");
        assert_z3_string_value(&z3_ast.nth_child(2).unwrap(), "else");
    }

    #[test]
    fn ite_symbols() {
        let ctx = Context::new();
        let c = ctx.bools("c").unwrap();
        let a = ctx.strings("a").unwrap();
        let b = ctx.strings("b").unwrap();
        let ite = ctx.ite(c, a, b).unwrap();
        let z3_ast = ite.to_z3().unwrap();

        assert_eq!(z3_ast.safe_decl().unwrap().kind(), z3::DeclKind::ITE);
        assert_eq!(z3_ast.nth_child(0).unwrap().safe_decl().unwrap().name(), "c");
        assert_eq!(z3_ast.nth_child(1).unwrap().safe_decl().unwrap().name(), "a");
        assert_eq!(z3_ast.nth_child(2).unwrap().safe_decl().unwrap().name(), "b");
    }
}

// ---------------------------------------------------------------
// from_z3 tests
// ---------------------------------------------------------------
mod from_z3 {
    use super::*;

    // -- Leaf nodes --

    #[test]
    fn symbol() {
        let ctx = Context::new();
        let z3_ast = Dynamic::from(z3::ast::String::new_const("x"));
        let result = StringAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx.strings("x").unwrap();
        assert_eq!(expected, result);
    }

    #[test]
    fn value_simple() {
        let ctx = Context::new();
        let z3_ast = Dynamic::from(z3::ast::String::from("hello"));
        let result = StringAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx.stringv("hello").unwrap();
        assert_eq!(expected, result);
    }

    #[test]
    fn value_empty() {
        let ctx = Context::new();
        let z3_ast = Dynamic::from(z3::ast::String::from(""));
        let result = StringAst::from_z3(&ctx, z3_ast).unwrap();
        let expected = ctx.stringv("").unwrap();
        assert_eq!(expected, result);
    }

    // -- StrConcat --

    #[test]
    fn concat() {
        let ctx = Context::new();
        let a_str = z3::ast::String::from("hello");
        let b_str = z3::ast::String::from(" world");
        let z3_cat = Dynamic::from(z3::ast::String::concat(&[a_str, b_str]));
        let result = StringAst::from_z3(&ctx, z3_cat).unwrap();
        let expected = ctx
            .str_concat(
                ctx.stringv("hello").unwrap(),
                ctx.stringv(" world").unwrap(),
            )
            .unwrap();
        assert_eq!(expected, result);
    }

    #[test]
    fn concat_symbols() {
        let ctx = Context::new();
        let a_str = z3::ast::String::new_const("a");
        let b_str = z3::ast::String::new_const("b");
        let z3_cat = Dynamic::from(z3::ast::String::concat(&[a_str, b_str]));
        let result = StringAst::from_z3(&ctx, z3_cat).unwrap();
        let expected = ctx
            .str_concat(ctx.strings("a").unwrap(), ctx.strings("b").unwrap())
            .unwrap();
        assert_eq!(expected, result);
    }

    // -- StrSubstr --

    #[test]
    fn substr() {
        let ctx = Context::new();
        let a_str = z3::ast::String::from("hello world");
        let offset_int = Int::from_i64(6);
        let len_int = Int::from_i64(5);
        let z3_sub = Dynamic::from(a_str.substr(offset_int, len_int));
        let result = StringAst::from_z3(&ctx, z3_sub).unwrap();
        let expected = ctx
            .str_substr(
                ctx.stringv("hello world").unwrap(),
                ctx.bvv_prim(6u64).unwrap(),
                ctx.bvv_prim(5u64).unwrap(),
            )
            .unwrap();
        assert_eq!(expected, result);
    }

    // -- StrReplace --

    #[test]
    fn replace() {
        let ctx = Context::new();
        let a_str = z3::ast::String::from("hello world");
        let b_str = z3::ast::String::from("world");
        let c_str = z3::ast::String::from("there");
        let z3_rep = Dynamic::from(crate::astext::string::str_replace_z3(&a_str, &b_str, &c_str));
        let result = StringAst::from_z3(&ctx, z3_rep).unwrap();
        let expected = ctx
            .str_replace(
                ctx.stringv("hello world").unwrap(),
                ctx.stringv("world").unwrap(),
                ctx.stringv("there").unwrap(),
            )
            .unwrap();
        assert_eq!(expected, result);
    }

    // -- ITE --

    #[test]
    fn ite() {
        let ctx = Context::new();
        let c = Bool::new_const("c");
        let t = z3::ast::String::from("then");
        let e = z3::ast::String::from("else");
        let t_dyn = Dynamic::from(t);
        let e_dyn = Dynamic::from(e);
        let z3_ite = c.ite(&t_dyn, &e_dyn);
        let result = StringAst::from_z3(&ctx, z3_ite).unwrap();
        let expected = ctx
            .ite(
                ctx.bools("c").unwrap(),
                ctx.stringv("then").unwrap(),
                ctx.stringv("else").unwrap(),
            )
            .unwrap();
        assert_eq!(expected, result);
    }

    #[test]
    fn ite_symbols() {
        let ctx = Context::new();
        let c = Bool::new_const("c");
        let a = Dynamic::from(z3::ast::String::new_const("a"));
        let b = Dynamic::from(z3::ast::String::new_const("b"));
        let z3_ite = c.ite(&a, &b);
        let result = StringAst::from_z3(&ctx, z3_ite).unwrap();
        let expected = ctx
            .ite(
                ctx.bools("c").unwrap(),
                ctx.strings("a").unwrap(),
                ctx.strings("b").unwrap(),
            )
            .unwrap();
        assert_eq!(expected, result);
    }
}

// ---------------------------------------------------------------
// roundtrip tests
// ---------------------------------------------------------------
mod roundtrip {
    use super::*;

    // -- Leaf nodes --

    #[test]
    fn symbol() {
        let ctx = Context::new();
        let ast = ctx.strings("x").unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn symbol_long_name() {
        let ctx = Context::new();
        let ast = ctx.strings("my_string_variable").unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn value_simple() {
        let ctx = Context::new();
        let ast = ctx.stringv("hello").unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn value_empty() {
        let ctx = Context::new();
        let ast = ctx.stringv("").unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn value_with_spaces() {
        let ctx = Context::new();
        let ast = ctx.stringv("hello world").unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn value_single_char() {
        let ctx = Context::new();
        let ast = ctx.stringv("a").unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn value_digits() {
        let ctx = Context::new();
        let ast = ctx.stringv("12345").unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn value_special_chars() {
        let ctx = Context::new();
        let ast = ctx.stringv("hello\tworld\n").unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- StrConcat --

    #[test]
    fn concat_values() {
        let ctx = Context::new();
        let s1 = ctx.stringv("hello").unwrap();
        let s2 = ctx.stringv(" world").unwrap();
        let ast = ctx.str_concat(s1, s2).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn concat_symbols() {
        let ctx = Context::new();
        let s1 = ctx.strings("a").unwrap();
        let s2 = ctx.strings("b").unwrap();
        let ast = ctx.str_concat(s1, s2).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn concat_mixed() {
        let ctx = Context::new();
        let s1 = ctx.strings("x").unwrap();
        let s2 = ctx.stringv("_suffix").unwrap();
        let ast = ctx.str_concat(s1, s2).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn concat_empty() {
        let ctx = Context::new();
        let s1 = ctx.stringv("hello").unwrap();
        let s2 = ctx.stringv("").unwrap();
        let ast = ctx.str_concat(s1, s2).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- StrSubstr --

    #[test]
    fn substr_value() {
        let ctx = Context::new();
        let s = ctx.stringv("hello world").unwrap();
        let start = ctx.bvv_prim(6u64).unwrap();
        let length = ctx.bvv_prim(5u64).unwrap();
        let ast = ctx.str_substr(s, start, length).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn substr_symbol() {
        let ctx = Context::new();
        let s = ctx.strings("s").unwrap();
        let start = ctx.bvv_prim(0u64).unwrap();
        let length = ctx.bvv_prim(3u64).unwrap();
        let ast = ctx.str_substr(s, start, length).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn substr_from_start() {
        let ctx = Context::new();
        let s = ctx.stringv("abcdef").unwrap();
        let start = ctx.bvv_prim(0u64).unwrap();
        let length = ctx.bvv_prim(3u64).unwrap();
        let ast = ctx.str_substr(s, start, length).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- StrReplace --

    #[test]
    fn replace_values() {
        let ctx = Context::new();
        let s = ctx.stringv("hello world").unwrap();
        let pat = ctx.stringv("world").unwrap();
        let rep = ctx.stringv("there").unwrap();
        let ast = ctx.str_replace(s, pat, rep).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn replace_symbols() {
        let ctx = Context::new();
        let s = ctx.strings("s").unwrap();
        let pat = ctx.strings("p").unwrap();
        let rep = ctx.strings("r").unwrap();
        let ast = ctx.str_replace(s, pat, rep).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn replace_with_empty() {
        let ctx = Context::new();
        let s = ctx.stringv("hello world").unwrap();
        let pat = ctx.stringv("world").unwrap();
        let rep = ctx.stringv("").unwrap();
        let ast = ctx.str_replace(s, pat, rep).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- ITE --

    #[test]
    fn ite_values() {
        let ctx = Context::new();
        let c = ctx.bools("c").unwrap();
        let then = ctx.stringv("then").unwrap();
        let else_ = ctx.stringv("else").unwrap();
        let ast = ctx.ite(c, then, else_).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn ite_symbols() {
        let ctx = Context::new();
        let c = ctx.bools("c").unwrap();
        let a = ctx.strings("a").unwrap();
        let b = ctx.strings("b").unwrap();
        let ast = ctx.ite(c, a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn ite_mixed() {
        let ctx = Context::new();
        let c = ctx.bools("c").unwrap();
        let a = ctx.strings("x").unwrap();
        let b = ctx.stringv("default").unwrap();
        let ast = ctx.ite(c, a, b).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    // -- BVToStr --

    #[test]
    fn bv_to_str_symbol() {
        let ctx = Context::new();
        let bv = ctx.bvs("x", 64).unwrap();
        let ast = ctx.bv_to_str(bv).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }

    #[test]
    fn bv_to_str_value() {
        let ctx = Context::new();
        let bv = ctx.bvv_prim(42u64).unwrap();
        let ast = ctx.bv_to_str(bv).unwrap();
        assert_eq!(ast, round_trip(&ctx, &ast).unwrap());
    }
}
