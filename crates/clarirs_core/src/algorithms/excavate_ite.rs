use std::sync::Arc;

use crate::{
    algorithms::{reconstruct::reconstruct_node, walk_post_order},
    ast::op::AstOp,
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
        // A frame of the explicit stack that hoists `ITE`s out of a single node
        // whose children have already been excavated. `Expand` holds a
        // child-list still to be distributed; `Combine` rebuilds an
        // `ITE(cond, then, else)` once both of its branches have been expanded.
        enum Frame<'a> {
            Expand(Vec<AstRef<'a>>),
            Combine(AstRef<'a>),
        }

        walk_post_order(
            self.clone(),
            |node, children| {
                let ctx = node.context();

                // An `ITE` is already in excavated form, so leave its branches
                // in place and just rebuild it from its excavated children.
                if matches!(node.op(), AstOp::ITE(..)) {
                    return reconstruct_node(ctx, &node, children);
                }

                // For any other op, distribute it over its `ITE` children:
                //   op(.., ITE(c, t, e), ..) -> ITE(c, op(.., t, ..), op(.., e, ..))
                // Because every op shares one enum and children are rebuilt
                // uniformly via `reconstruct_node`, the per-sort distribution
                // rules collapse into this single loop. The transform is
                // naturally recursive (each branch may expose further `ITE`s),
                // but a closure can't call itself, so we drive it with an
                // explicit stack: `Expand` a child-list down to its first `ITE`,
                // then `Combine` the two expanded branches back under `cond`.
                let mut work = vec![Frame::Expand(children.to_vec())];
                let mut done: Vec<AstRef<'c>> = Vec::new();

                while let Some(frame) = work.pop() {
                    match frame {
                        Frame::Expand(branch) => {
                            match branch.iter().position(|c| matches!(c.op(), AstOp::ITE(..))) {
                                // No `ITE` left: a leaf of the decision tree, so
                                // rebuild the node with this concrete child-list.
                                None => done.push(reconstruct_node(ctx, &node, &branch)?),
                                // Split on the first `ITE` child, then expand the
                                // `then`/`else` child-lists and combine them.
                                Some(idx) => {
                                    let (cond, then_, else_) = match branch[idx].op() {
                                        AstOp::ITE(cond, then_, else_) => {
                                            (cond.clone(), then_.clone(), else_.clone())
                                        }
                                        _ => unreachable!(),
                                    };
                                    let mut else_branch = branch;
                                    let mut then_branch = else_branch.clone();
                                    then_branch[idx] = then_;
                                    else_branch[idx] = else_;
                                    // Push `then` last so it is expanded first;
                                    // `Combine` then pops `else` above `then`.
                                    work.push(Frame::Combine(cond));
                                    work.push(Frame::Expand(else_branch));
                                    work.push(Frame::Expand(then_branch));
                                }
                            }
                        }
                        Frame::Combine(cond) => {
                            let else_branch = done.pop().expect("else branch expanded");
                            let then_branch = done.pop().expect("then branch expanded");
                            done.push(ctx.ite(cond, then_branch, else_branch)?);
                        }
                    }
                }

                Ok(done.pop().expect("expansion yields exactly one result"))
            },
            &self.context().excavate_ite_cache,
        )
    }
}

#[cfg(test)]
mod tests;
