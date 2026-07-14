use std::collections::BTreeSet;
use std::sync::Arc;

use crate::{
    algorithms::{
        reconstruct::{rebuild_op, reconstruct_node},
        walk_post_order,
    },
    ast::op::AstOp,
    cache::Cache,
    context::structural_hash,
    prelude::*,
};

impl<'c> AstNode<'c> {
    /// Excavates if-then-else expressions to the top level of the AST.
    ///
    /// Returns a semantically equivalent AST where nested ITE expressions have
    /// been "excavated" (moved up) to the top level where possible. For
    /// example, `a + (if cond then b else c)` becomes
    /// `if cond then (a + b) else (a + c)`.
    pub fn excavate_ite(self: &Arc<Self>) -> Result<AstRef<'c>, ClarirsError> {
        walk_post_order(
            self.clone(),
            |node, children| excavate_node(&node, children),
            &self.context().excavate_ite_cache,
        )
    }
}

/// Hoists `ITE`s out of a single node whose children have already been
/// excavated. Because every operation now shares one op enum and children are
/// rebuilt uniformly via [`reconstruct_node`], the per-sort distribution rules
/// (`op(.., ITE(c, t, e), ..) -> ITE(c, op(.., t, ..), op(.., e, ..))`) collapse
/// into this single routine.
///
/// An `ITE` is already in excavated form, so its branches are left in place;
/// for any other op we distribute over its first `ITE` child and recurse to
/// hoist any remaining ones, yielding the fully expanded decision tree.
fn excavate_node<'c>(
    ast: &AstRef<'c>,
    children: &[AstRef<'c>],
) -> Result<AstRef<'c>, ClarirsError> {
    let ctx = ast.context();

    if matches!(ast.op(), AstOp::ITE(..)) {
        return reconstruct_node(ctx, ast, children);
    }

    let idx = match children
        .iter()
        .position(|c| matches!(c.op(), AstOp::ITE(..)))
    {
        Some(idx) => idx,
        None => return reconstruct_node(ctx, ast, children),
    };

    let op = rebuild_op(ast, children).expect("a node being distributed is not a leaf");
    let key = structural_hash(op.infer_type(), &op, &BTreeSet::new());
    if let Some(cached) = ctx.excavate_ite_cache.get(&key) {
        return Ok(cached);
    }

    let (cond, then_, else_) = match children[idx].op() {
        AstOp::ITE(cond, then_, else_) => (cond.clone(), then_.clone(), else_.clone()),
        _ => unreachable!(),
    };
    let mut branch = children.to_vec();
    branch[idx] = then_;
    let then_branch = excavate_node(ast, &branch)?;
    branch[idx] = else_;
    let else_branch = excavate_node(ast, &branch)?;
    let result = ctx.ite(cond, then_branch, else_branch)?;

    ctx.excavate_ite_cache.insert(key, &result);
    Ok(result)
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    #[test]
    fn test_bitvec_not_with_ite() {
        let ctx = Context::new();

        // Create variables
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let c = ctx.bools("c").unwrap();

        // Create expression: not(if c then a else b)
        let ite = ctx.ite(&c, &a, &b).unwrap();
        let expr = ctx.not(&ite).unwrap();

        // Expected result: if c then not(a) else not(b)
        let not_a = ctx.not(&a).unwrap();
        let not_b = ctx.not(&b).unwrap();
        let expected = ctx.ite(&c, &not_a, &not_b).unwrap();

        // Excavate ITEs
        let result = expr.excavate_ite().unwrap();

        // Verify result
        assert_eq!(result.op(), expected.op());
    }

    #[test]
    fn test_bitvec_neg_with_ite() {
        let ctx = Context::new();

        // Create variables
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let c = ctx.bools("c").unwrap();

        // Create expression: neg(if c then a else b)
        let ite = ctx.ite(&c, &a, &b).unwrap();
        let expr = ctx.neg(&ite).unwrap();

        // Expected result: if c then neg(a) else neg(b)
        let neg_a = ctx.neg(&a).unwrap();
        let neg_b = ctx.neg(&b).unwrap();
        let expected = ctx.ite(&c, &neg_a, &neg_b).unwrap();

        // Excavate ITEs
        let result = expr.excavate_ite().unwrap();

        // Verify result
        assert_eq!(result.op(), expected.op());
    }

    #[test]
    fn test_bitvec_add_with_ite() {
        let ctx = Context::new();

        // Create variables
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let c = ctx.bools("c").unwrap();
        let d = ctx.bvs("d", 32).unwrap();

        // Create expression: d + (if c then a else b)
        let ite = ctx.ite(&c, &a, &b).unwrap();
        let expr = ctx.add(&d, &ite).unwrap();

        // Expected result: if c then (d + a) else (d + b)
        let d_add_a = ctx.add(&d, &a).unwrap();
        let d_add_b = ctx.add(&d, &b).unwrap();
        let expected = ctx.ite(&c, &d_add_a, &d_add_b).unwrap();

        // Excavate ITEs
        let result = expr.excavate_ite().unwrap();

        // Verify result
        assert_eq!(result.op(), expected.op());
    }

    #[test]
    fn test_bitvec_sub_with_ite() {
        let ctx = Context::new();

        // Create variables
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let c = ctx.bools("c").unwrap();
        let d = ctx.bvs("d", 32).unwrap();

        // Create expression: d - (if c then a else b)
        let ite = ctx.ite(&c, &a, &b).unwrap();
        let expr = ctx.sub(&d, &ite).unwrap();

        // Expected result: if c then (d - a) else (d - b)
        let d_sub_a = ctx.sub(&d, &a).unwrap();
        let d_sub_b = ctx.sub(&d, &b).unwrap();
        let expected = ctx.ite(&c, &d_sub_a, &d_sub_b).unwrap();

        // Excavate ITEs
        let result = expr.excavate_ite().unwrap();

        // Verify result
        assert_eq!(result.op(), expected.op());
    }

    #[test]
    fn test_bitvec_mul_with_ite() {
        let ctx = Context::new();

        // Create variables
        let a = ctx.bvs("a", 32).unwrap();
        let b = ctx.bvs("b", 32).unwrap();
        let c = ctx.bools("c").unwrap();
        let d = ctx.bvs("d", 32).unwrap();

        // Create expression: d * (if c then a else b)
        let ite = ctx.ite(&c, &a, &b).unwrap();
        let expr = ctx.mul(&d, &ite).unwrap();

        // Expected result: if c then (d * a) else (d * b)
        let d_mul_a = ctx.mul(&d, &a).unwrap();
        let d_mul_b = ctx.mul(&d, &b).unwrap();
        let expected = ctx.ite(&c, &d_mul_a, &d_mul_b).unwrap();

        // Excavate ITEs
        let result = expr.excavate_ite().unwrap();

        // Verify result
        assert_eq!(result.op(), expected.op());
    }

    #[test]
    fn test_bool_not_with_ite() {
        let ctx = Context::new();

        // Create variables
        let a = ctx.bools("a").unwrap();
        let b = ctx.bools("b").unwrap();
        let c = ctx.bools("c").unwrap();

        // Create expression: not(if c then a else b)
        let ite = ctx.ite(&c, &a, &b).unwrap();
        let expr = ctx.not(&ite).unwrap();

        // Expected result: if c then not(a) else not(b)
        let not_a = ctx.not(&a).unwrap();
        let not_b = ctx.not(&b).unwrap();
        let expected = ctx.ite(&c, &not_a, &not_b).unwrap();

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
        let ite = ctx.ite(&c, &a, &b).unwrap();
        let expr = ctx.and2(&d, &ite).unwrap();

        // Expected result: if c then (d && a) else (d && b)
        let d_and_a = ctx.and2(&d, &a).unwrap();
        let d_and_b = ctx.and2(&d, &b).unwrap();
        let expected = ctx.ite(&c, &d_and_a, &d_and_b).unwrap();

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
        let ite = ctx.ite(&c, &a, &b).unwrap();
        let expr = ctx.or2(&d, &ite).unwrap();

        // Expected result: if c then (d || a) else (d || b)
        let d_or_a = ctx.or2(&d, &a).unwrap();
        let d_or_b = ctx.or2(&d, &b).unwrap();
        let expected = ctx.ite(&c, &d_or_a, &d_or_b).unwrap();

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
        let ite = ctx.ite(&c, &a, &b).unwrap();
        let expr = ctx.xor2(&d, &ite).unwrap();

        // Expected result: if c then (d ^ a) else (d ^ b)
        let d_xor_a = ctx.xor2(&d, &a).unwrap();
        let d_xor_b = ctx.xor2(&d, &b).unwrap();
        let expected = ctx.ite(&c, &d_xor_a, &d_xor_b).unwrap();

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
        let ite1 = ctx.ite(&c, &a, &b).unwrap();
        let ite2 = ctx.ite(&d, &b, &a).unwrap();
        let expr = ctx.and2(&ite1, &ite2).unwrap();

        // Expected result:
        // if c then
        //   (if d then (a && b) else (a && a))
        // else
        //   (if d then (b && b) else (b && a))
        let a_and_b = ctx.and2(&a, &b).unwrap();
        let a_and_a = ctx.and2(&a, &a).unwrap();
        let b_and_b = ctx.and2(&b, &b).unwrap();
        let b_and_a = ctx.and2(&b, &a).unwrap();

        let then_branch = ctx.ite(&d, &a_and_b, &a_and_a).unwrap();
        let else_branch = ctx.ite(&d, &b_and_b, &b_and_a).unwrap();

        let expected = ctx.ite(&c, &then_branch, &else_branch).unwrap();

        // Excavate ITEs
        let result = expr.excavate_ite().unwrap();

        // Verify result
        assert_eq!(result.op(), expected.op());
    }
}
