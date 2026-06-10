use crate::{
    algorithms::{reconstruct::reconstruct_node, walk_post_order},
    ast::op::AstOp,
    prelude::*,
};

/// Trait for excavating if-then-else expressions to the top level of an AST.
///
/// This transformation takes an AST containing nested ITE expressions and returns
/// an equivalent AST where the ITE expressions have been "excavated" (moved up) to the top level.
///
/// For example, if we have an expression like: `a + (if cond then b else c)`
///
/// After excavation, it would become: `if cond then (a + b) else (a + c)`
pub trait ExcavateIte<'c>: Sized {
    /// Transforms the AST by moving ITE expressions to the top level.
    ///
    /// Returns a new AST that is semantically equivalent to the original,
    /// but with ITE expressions moved to the top level where possible.
    fn excavate_ite(&self) -> Result<Self, ClarirsError>;
}

impl<'c> ExcavateIte<'c> for AstRef<'c> {
    fn excavate_ite(&self) -> Result<Self, ClarirsError> {
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

    match children
        .iter()
        .position(|c| matches!(c.op(), AstOp::ITE(..)))
    {
        Some(idx) => {
            let (cond, then_, else_) = match children[idx].op() {
                AstOp::ITE(cond, then_, else_) => (cond.clone(), then_.clone(), else_.clone()),
                _ => unreachable!(),
            };
            let mut branch = children.to_vec();
            branch[idx] = then_;
            let then_branch = excavate_node(ast, &branch)?;
            branch[idx] = else_;
            let else_branch = excavate_node(ast, &branch)?;
            ctx.ite(cond, then_branch, else_branch)
        }
        None => reconstruct_node(ctx, ast, children),
    }
}

#[cfg(test)]
mod tests;
