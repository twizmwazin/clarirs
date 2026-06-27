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
///
/// The intermediate child arrays produced by that recursion never correspond to
/// a real input node, so they cannot be short-circuited by [`walk_post_order`]'s
/// keyed-by-input-node cache. We instead memoize them in the same
/// `excavate_ite_cache`, keyed by the structural hash of the op-shape being
/// distributed. Sharing one map is sound because that is exactly the key space
/// `walk_post_order` already uses (a node's hash *is* its structural hash), and
/// structurally identical shapes always excavate to the same result — so any
/// key that coincides legitimately maps to one value.
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
mod tests;
