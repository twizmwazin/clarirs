use crate::{algorithms::ExcavateIte, prelude::*};

#[test]
fn test_bool_not_with_ite() {
    let ctx = Context::new();

    // Create variables
    let a = ctx.bools("a").unwrap();
    let b = ctx.bools("b").unwrap();
    let c = ctx.bools("c").unwrap();

    // Create expression: not(if c then a else b)
    let ite = ctx.if_(&c, &a, &b).unwrap();
    let expr = ctx.not(&ite).unwrap();

    // Expected result: if c then not(a) else not(b)
    let not_a = ctx.not(&a).unwrap();
    let not_b = ctx.not(&b).unwrap();
    let expected = ctx.if_(&c, &not_a, &not_b).unwrap();

    // Excavate ITEs
    let result = expr.excavate_ite().unwrap();

    // Verify result
    assert_eq!(result.op(), expected.op());
}

#[test]
fn test_bool_and_with_ite() {
    let ctx = Context::new();

    // Create variables
    let a = ctx.bools("a").unwrap();
    let b = ctx.bools("b").unwrap();
    let c = ctx.bools("c").unwrap();
    let d = ctx.bools("d").unwrap();

    // Create expression: d && (if c then a else b)
    let ite = ctx.if_(&c, &a, &b).unwrap();
    let expr = ctx.and(&d, &ite).unwrap();

    // Expected result: if c then (d && a) else (d && b)
    let d_and_a = ctx.and(&d, &a).unwrap();
    let d_and_b = ctx.and(&d, &b).unwrap();
    let expected = ctx.if_(&c, &d_and_a, &d_and_b).unwrap();

    // Excavate ITEs
    let result = expr.excavate_ite().unwrap();

    // Verify result
    assert_eq!(result.op(), expected.op());
}

#[test]
fn test_bool_or_with_ite() {
    let ctx = Context::new();

    // Create variables
    let a = ctx.bools("a").unwrap();
    let b = ctx.bools("b").unwrap();
    let c = ctx.bools("c").unwrap();
    let d = ctx.bools("d").unwrap();

    // Create expression: d || (if c then a else b)
    let ite = ctx.if_(&c, &a, &b).unwrap();
    let expr = ctx.or(&d, &ite).unwrap();

    // Expected result: if c then (d || a) else (d || b)
    let d_or_a = ctx.or(&d, &a).unwrap();
    let d_or_b = ctx.or(&d, &b).unwrap();
    let expected = ctx.if_(&c, &d_or_a, &d_or_b).unwrap();

    // Excavate ITEs
    let result = expr.excavate_ite().unwrap();

    // Verify result
    assert_eq!(result.op(), expected.op());
}

#[test]
fn test_bool_xor_with_ite() {
    let ctx = Context::new();

    // Create variables
    let a = ctx.bools("a").unwrap();
    let b = ctx.bools("b").unwrap();
    let c = ctx.bools("c").unwrap();
    let d = ctx.bools("d").unwrap();

    // Create expression: d ^ (if c then a else b)
    let ite = ctx.if_(&c, &a, &b).unwrap();
    let expr = ctx.xor(&d, &ite).unwrap();

    // Expected result: if c then (d ^ a) else (d ^ b)
    let d_xor_a = ctx.xor(&d, &a).unwrap();
    let d_xor_b = ctx.xor(&d, &b).unwrap();
    let expected = ctx.if_(&c, &d_xor_a, &d_xor_b).unwrap();

    // Excavate ITEs
    let result = expr.excavate_ite().unwrap();

    // Verify result
    assert_eq!(result.op(), expected.op());
}

#[test]
fn test_nested_bool_ite() {
    let ctx = Context::new();

    // Create variables
    let a = ctx.bools("a").unwrap();
    let b = ctx.bools("b").unwrap();
    let c = ctx.bools("c").unwrap();
    let d = ctx.bools("d").unwrap();

    // Create expression: (if c then a else b) && (if d then b else a)
    let ite1 = ctx.if_(&c, &a, &b).unwrap();
    let ite2 = ctx.if_(&d, &b, &a).unwrap();
    let expr = ctx.and(&ite1, &ite2).unwrap();

    // Expected result:
    // if c then
    //   (if d then (a && b) else (a && a))
    // else
    //   (if d then (b && b) else (b && a))
    let a_and_b = ctx.and(&a, &b).unwrap();
    let a_and_a = ctx.and(&a, &a).unwrap();
    let b_and_b = ctx.and(&b, &b).unwrap();
    let b_and_a = ctx.and(&b, &a).unwrap();

    let then_branch = ctx.if_(&d, &a_and_b, &a_and_a).unwrap();
    let else_branch = ctx.if_(&d, &b_and_b, &b_and_a).unwrap();

    let expected = ctx.if_(&c, &then_branch, &else_branch).unwrap();

    // Excavate ITEs
    let result = expr.excavate_ite().unwrap();

    // Verify result
    assert_eq!(result.op(), expected.op());
}
