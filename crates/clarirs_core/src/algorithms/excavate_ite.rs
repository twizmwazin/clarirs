use crate::algorithms::reconstruct::reconstruct_node;
use crate::prelude::*;

use super::walk_post_order;

/// Trait for excavating if-then-else expressions to the top level of an AST.
///
/// This transformation takes an AST containing nested ITE expressions and returns
/// an equivalent AST where the ITE expressions have been "excavated" (moved up) to the top level.
///
/// For example, if we have an expression like: `a + (if cond then b else c)`
///
/// After excavation, it would become: `if cond then (a + b) else (a + c)`
pub trait ExcavateIte<'c>: Sized {
    fn excavate_ite(&self) -> Result<Self, ClarirsError>;
}

impl<'c> ExcavateIte<'c> for AstRef<'c> {
    fn excavate_ite(&self) -> Result<Self, ClarirsError> {
        walk_post_order(
            self.clone(),
            |node, children| excavate_ite_node(&node, children),
            &self.context().excavate_ite_cache,
        )
    }
}

fn excavate_ite_node<'c>(
    ast: &AstRef<'c>,
    children: &[AstRef<'c>],
) -> Result<AstRef<'c>, ClarirsError> {
    let ctx = ast.context();

    // Leaves: return as-is
    if ast.op().is_leaf() {
        return Ok(ast.clone());
    }

    // ITE itself: just rebuild from transformed children
    if let Op::ITE(..) = ast.op() {
        return ctx.ite(
            children[0].clone(),
            children[1].clone(),
            children[2].clone(),
        );
    }

    // Find the first ITE child and split on it.
    let ite_idx = children
        .iter()
        .position(|c| matches!(c.op(), Op::ITE(..)));

    let Some(idx) = ite_idx else {
        // No ITE children — rebuild the node with transformed children
        return reconstruct_node(ctx, ast, children);
    };

    let Op::ITE(cond, then_, else_) = children[idx].op() else {
        unreachable!()
    };

    // Build then-branch: replace the ITE child with its then-value
    let mut then_children = children.to_vec();
    then_children[idx] = then_.clone();
    let then_branch = reconstruct_node(ctx, ast, &then_children)?;

    // Build else-branch: replace the ITE child with its else-value
    let mut else_children = children.to_vec();
    else_children[idx] = else_.clone();
    let else_branch = reconstruct_node(ctx, ast, &else_children)?;

    // Recursively excavate the branches (they may still contain ITE children)
    let then_excavated = then_branch.excavate_ite()?;
    let else_excavated = else_branch.excavate_ite()?;

    ctx.ite(cond, then_excavated, else_excavated)
}

#[cfg(test)]
mod tests;
