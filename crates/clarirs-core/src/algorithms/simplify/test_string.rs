use crate::prelude::*;
use anyhow::Result;

// -- StringV / StringS --

#[test]
fn test_string_prim() -> Result<()> {
    let ctx = Context::new();

    let concrete = ctx.stringv("hello")?;
    let symbolic = ctx.strings("s")?;

    assert_eq!(concrete.simplify()?, concrete);
    assert_eq!(symbolic.simplify()?, symbolic);

    Ok(())
}

// -- StrConcat --

#[test]
fn test_concat_concrete() -> Result<()> {
    let ctx = Context::new();

    let result = ctx
        .str_concat(ctx.stringv("hello")?, ctx.stringv(" world")?)?
        .simplify()?;
    assert_eq!(result, ctx.stringv("hello world")?);

    // Empty operands
    let result = ctx
        .str_concat(ctx.stringv("")?, ctx.stringv("abc")?)?
        .simplify()?;
    assert_eq!(result, ctx.stringv("abc")?);

    let result = ctx
        .str_concat(ctx.stringv("")?, ctx.stringv("")?)?
        .simplify()?;
    assert_eq!(result, ctx.stringv("")?);

    // Multi-byte UTF-8 operands are concatenated bytewise-correctly
    let result = ctx
        .str_concat(ctx.stringv("héllo")?, ctx.stringv("日本語")?)?
        .simplify()?;
    assert_eq!(result, ctx.stringv("héllo日本語")?);

    Ok(())
}

#[test]
fn test_concat_nested_concrete() -> Result<()> {
    let ctx = Context::new();

    // concat(concat("a", "b"), "c") fully folds to "abc"
    let inner = ctx.str_concat(ctx.stringv("a")?, ctx.stringv("b")?)?;
    let result = ctx.str_concat(inner, ctx.stringv("c")?)?.simplify()?;
    assert_eq!(result, ctx.stringv("abc")?);

    Ok(())
}

#[test]
fn test_concat_symbolic_fallback() -> Result<()> {
    let ctx = Context::new();

    let s = ctx.strings("s")?;

    // Symbolic operand: op is preserved
    let result = ctx.str_concat(&s, ctx.stringv("x")?)?.simplify()?;
    assert!(matches!(result.op(), AstOp::StrConcat(..)));
    assert_eq!(result, ctx.str_concat(&s, ctx.stringv("x")?)?);

    // Children are still simplified inside the preserved op
    let inner = ctx.str_concat(ctx.stringv("a")?, ctx.stringv("b")?)?;
    let result = ctx.str_concat(&s, inner)?.simplify()?;
    assert_eq!(result, ctx.str_concat(&s, ctx.stringv("ab")?)?);

    Ok(())
}

// -- StrSubstr --

#[test]
fn test_substr_concrete() -> Result<()> {
    let ctx = Context::new();

    let s = ctx.stringv("hello world")?;

    let result = ctx
        .str_substr(
            &s,
            ctx.bvv(BitVec::from((6u64, 64)))?,
            ctx.bvv(BitVec::from((5u64, 64)))?,
        )?
        .simplify()?;
    assert_eq!(result, ctx.stringv("world")?);

    let result = ctx
        .str_substr(
            &s,
            ctx.bvv(BitVec::from((0u64, 64)))?,
            ctx.bvv(BitVec::from((5u64, 64)))?,
        )?
        .simplify()?;
    assert_eq!(result, ctx.stringv("hello")?);

    Ok(())
}

#[test]
fn test_substr_zero_length() -> Result<()> {
    let ctx = Context::new();

    let result = ctx
        .str_substr(
            ctx.stringv("hello")?,
            ctx.bvv(BitVec::from((2u64, 64)))?,
            ctx.bvv(BitVec::from((0u64, 64)))?,
        )?
        .simplify()?;
    assert_eq!(result, ctx.stringv("")?);

    Ok(())
}

#[test]
fn test_substr_out_of_bounds_start() -> Result<()> {
    let ctx = Context::new();

    let s = ctx.stringv("hello")?;

    // start == length of string -> empty
    let result = ctx
        .str_substr(
            &s,
            ctx.bvv(BitVec::from((5u64, 64)))?,
            ctx.bvv(BitVec::from((1u64, 64)))?,
        )?
        .simplify()?;
    assert_eq!(result, ctx.stringv("")?);

    // A "negative" index wrapped to 2^64-1 -> empty
    let result = ctx
        .str_substr(
            &s,
            ctx.bvv(BitVec::from((u64::MAX, 64)))?,
            ctx.bvv(BitVec::from((1u64, 64)))?,
        )?
        .simplify()?;
    assert_eq!(result, ctx.stringv("")?);

    Ok(())
}

#[test]
fn test_substr_length_exceeds_string() -> Result<()> {
    let ctx = Context::new();

    // Length running past the end is clamped to the end of the string
    let result = ctx
        .str_substr(
            ctx.stringv("hello world")?,
            ctx.bvv(BitVec::from((6u64, 64)))?,
            ctx.bvv(BitVec::from((100u64, 64)))?,
        )?
        .simplify()?;
    assert_eq!(result, ctx.stringv("world")?);

    Ok(())
}

#[test]
fn test_substr_multibyte_utf8() -> Result<()> {
    let ctx = Context::new();

    // Indices are character-based, not byte-based.
    // "héllo": 'é' is 2 bytes in UTF-8.
    let result = ctx
        .str_substr(
            ctx.stringv("héllo")?,
            ctx.bvv(BitVec::from((1u64, 64)))?,
            ctx.bvv(BitVec::from((2u64, 64)))?,
        )?
        .simplify()?;
    assert_eq!(result, ctx.stringv("él")?);

    // "日本語abc": each CJK char is 3 bytes.
    let result = ctx
        .str_substr(
            ctx.stringv("日本語abc")?,
            ctx.bvv(BitVec::from((1u64, 64)))?,
            ctx.bvv(BitVec::from((3u64, 64)))?,
        )?
        .simplify()?;
    assert_eq!(result, ctx.stringv("本語a")?);

    Ok(())
}

#[test]
fn test_substr_symbolic_fallback() -> Result<()> {
    let ctx = Context::new();

    // Symbolic string base
    let result = ctx
        .str_substr(
            ctx.strings("s")?,
            ctx.bvv(BitVec::from((0u64, 64)))?,
            ctx.bvv(BitVec::from((3u64, 64)))?,
        )?
        .simplify()?;
    assert!(matches!(result.op(), AstOp::StrSubstr(..)));

    // Symbolic start index
    let result = ctx
        .str_substr(
            ctx.stringv("hello")?,
            ctx.bvs("start", 64)?,
            ctx.bvv(BitVec::from((3u64, 64)))?,
        )?
        .simplify()?;
    assert!(matches!(result.op(), AstOp::StrSubstr(..)));

    Ok(())
}

// -- StrReplace --

#[test]
fn test_replace_first_occurrence_only() -> Result<()> {
    let ctx = Context::new();

    // Only the first occurrence is replaced (ClariPy semantics)
    let result = ctx
        .str_replace(ctx.stringv("aaa")?, ctx.stringv("a")?, ctx.stringv("b")?)?
        .simplify()?;
    assert_eq!(result, ctx.stringv("baa")?);

    let result = ctx
        .str_replace(
            ctx.stringv("hello world hello")?,
            ctx.stringv("hello")?,
            ctx.stringv("hi")?,
        )?
        .simplify()?;
    assert_eq!(result, ctx.stringv("hi world hello")?);

    Ok(())
}

#[test]
fn test_replace_no_match() -> Result<()> {
    let ctx = Context::new();

    let result = ctx
        .str_replace(
            ctx.stringv("hello")?,
            ctx.stringv("xyz")?,
            ctx.stringv("abc")?,
        )?
        .simplify()?;
    assert_eq!(result, ctx.stringv("hello")?);

    Ok(())
}

#[test]
fn test_replace_empty_pattern() -> Result<()> {
    let ctx = Context::new();

    // Rust's replacen with an empty pattern inserts at the beginning
    let result = ctx
        .str_replace(ctx.stringv("hello")?, ctx.stringv("")?, ctx.stringv("X")?)?
        .simplify()?;
    assert_eq!(result, ctx.stringv("Xhello")?);

    Ok(())
}

#[test]
fn test_replace_with_empty_replacement() -> Result<()> {
    let ctx = Context::new();

    let result = ctx
        .str_replace(
            ctx.stringv("hello world")?,
            ctx.stringv("o")?,
            ctx.stringv("")?,
        )?
        .simplify()?;
    assert_eq!(result, ctx.stringv("hell world")?);

    Ok(())
}

#[test]
fn test_replace_symbolic_fallback() -> Result<()> {
    let ctx = Context::new();

    let result = ctx
        .str_replace(
            ctx.strings("s")?,
            ctx.stringv("a")?,
            ctx.stringv("b")?,
        )?
        .simplify()?;
    assert!(matches!(result.op(), AstOp::StrReplace(..)));

    let result = ctx
        .str_replace(
            ctx.stringv("hello")?,
            ctx.strings("pat")?,
            ctx.stringv("b")?,
        )?
        .simplify()?;
    assert!(matches!(result.op(), AstOp::StrReplace(..)));

    Ok(())
}

// -- BVToStr --

#[test]
fn test_bv_to_str_concrete() -> Result<()> {
    let ctx = Context::new();

    let result = ctx
        .bv_to_str(ctx.bvv(BitVec::from((42u64, 64)))?)?
        .simplify()?;
    assert_eq!(result, ctx.stringv("42")?);

    let result = ctx
        .bv_to_str(ctx.bvv(BitVec::from((0u64, 8)))?)?
        .simplify()?;
    assert_eq!(result, ctx.stringv("0")?);

    // Value is interpreted as unsigned: 0xFF in 8 bits is 255, not -1
    let result = ctx
        .bv_to_str(ctx.bvv(BitVec::from((0xFFu64, 8)))?)?
        .simplify()?;
    assert_eq!(result, ctx.stringv("255")?);

    Ok(())
}

#[test]
fn test_bv_to_str_symbolic_fallback() -> Result<()> {
    let ctx = Context::new();

    let result = ctx.bv_to_str(ctx.bvs("x", 64)?)?.simplify()?;
    assert!(matches!(result.op(), AstOp::BVToStr(..)));

    Ok(())
}

// -- ITE --

#[test]
fn test_string_ite_concrete_condition() -> Result<()> {
    let ctx = Context::new();

    let then_ = ctx.stringv("then")?;
    let else_ = ctx.stringv("else")?;

    let result = ctx.ite(ctx.true_()?, &then_, &else_)?.simplify()?;
    assert_eq!(result, then_);

    let result = ctx.ite(ctx.false_()?, &then_, &else_)?.simplify()?;
    assert_eq!(result, else_);

    Ok(())
}

#[test]
fn test_string_ite_equal_branches() -> Result<()> {
    let ctx = Context::new();

    // With identical branches, the (symbolic) condition is dropped
    let branch = ctx.stringv("same")?;
    let result = ctx.ite(ctx.bools("c")?, &branch, &branch)?.simplify()?;
    assert_eq!(result, branch);

    // Branches that only become equal after simplification also collapse
    let concat = ctx.str_concat(ctx.stringv("sa")?, ctx.stringv("me")?)?;
    let result = ctx.ite(ctx.bools("c")?, concat, &branch)?.simplify()?;
    assert_eq!(result, branch);

    Ok(())
}

#[test]
fn test_string_ite_not_condition_inverts_branches() -> Result<()> {
    let ctx = Context::new();

    let c = ctx.bools("c")?;
    let a = ctx.stringv("a")?;
    let b = ctx.stringv("b")?;

    // ite(!c, a, b) => ite(c, b, a)
    let result = ctx.ite(ctx.not(&c)?, &a, &b)?.simplify()?;
    assert_eq!(result, ctx.ite(&c, &b, &a)?);

    Ok(())
}

#[test]
fn test_string_ite_symbolic_preserved() -> Result<()> {
    let ctx = Context::new();

    let expr = ctx.ite(ctx.bools("c")?, ctx.stringv("a")?, ctx.stringv("b")?)?;
    assert_eq!(expr.simplify()?, expr);

    Ok(())
}
