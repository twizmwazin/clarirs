//! Post-order traversal iterator for AST nodes.

use ahash::{HashSet, HashSetExt};

use super::{AstIterator, NodeState};
use crate::prelude::*;

/// An iterator that traverses an AST in post-order (children first, then parent).
///
/// This is useful for operations that need to process children before parents,
/// such as expression evaluation or AST transformations.
///
/// # Example
///
/// ```
/// use clarirs_core::prelude::*;
///
/// let ctx = Context::new();
/// let ast = ctx.add(
///     &ctx.bvs("a", 64).unwrap(),
///     &ctx.mul(&ctx.bvs("b", 64).unwrap(), &ctx.bvs("c", 64).unwrap()).unwrap(),
/// ).unwrap();
/// let var_ast = DynAst::from(&ast);
///
/// // Create an iterator that traverses the AST in post-order
/// let iter = PostOrderIter::from(var_ast);
///
/// // Collect nodes in post-order
/// let nodes: Vec<DynAst> = iter.collect();
/// ```
pub struct PostOrderIter<'c> {
    /// Stack of nodes to visit, with a state indicating whether the node's children have been pushed
    stack: Vec<(DynAst<'c>, NodeState)>,
    /// Set of nodes that have been processed to handle cycles
    processed: HashSet<DynAst<'c>>,
}

impl<'c> PostOrderIter<'c> {
    /// Creates a new post-order iterator from an AST node.
    pub fn new(ast: DynAst<'c>) -> Self {
        Self::from_ast(ast)
    }
}

impl<'c> AstIterator<'c> for PostOrderIter<'c> {
    fn from_ast(ast: DynAst<'c>) -> Self {
        let mut iter = PostOrderIter {
            stack: Vec::new(),
            processed: HashSet::new(),
        };

        // Push the initial node as discovered but not processed
        iter.stack.push((ast, NodeState::Discovered));

        iter
    }
}

impl<'c> From<DynAst<'c>> for PostOrderIter<'c> {
    fn from(value: DynAst<'c>) -> Self {
        Self::from_ast(value)
    }
}

impl<'c> Iterator for PostOrderIter<'c> {
    type Item = DynAst<'c>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((node, state)) = self.stack.pop() {
            match state {
                NodeState::Discovered => {
                    // Skip if we've already processed this node (handles cycles)
                    if self.processed.contains(&node) {
                        continue;
                    }

                    // We're seeing this node for the first time
                    // Push it back with the Processed state so we'll visit it again
                    // after processing all its children
                    self.stack.push((node.clone(), NodeState::Processed));

                    // Push all children onto the stack (in reverse order)
                    // so they'll be processed before the parent
                    let children = node.children();
                    for child in children.into_iter().rev() {
                        // Only push children we haven't fully processed yet
                        if !self.processed.contains(&child) {
                            self.stack.push((child, NodeState::Discovered));
                        }
                    }
                }
                NodeState::Processed => {
                    // We've already processed all children of this node
                    // Now we can return the node itself

                    // Mark as processed and return
                    self.processed.insert(node.clone());
                    return Some(node);
                }
            }
        }

        // No more nodes to process
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_postorder() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Create a simple AST: (a + (b * c))
        let a = ctx.bvs("a", 64)?;
        let b = ctx.bvs("b", 64)?;
        let c = ctx.bvs("c", 64)?;
        let b_mul_c = ctx.mul(&b, &c)?;
        let a_add_bc = ctx.add(&a, &b_mul_c)?;

        let var_ast = DynAst::from(&a_add_bc);

        // Collect nodes in postorder
        let nodes: Vec<DynAst> = PostOrderIter::from_ast(var_ast).collect();

        // We should have 5 nodes in total (a, b, c, b*c, a+(b*c))
        assert_eq!(nodes.len(), 5);

        // Simple test: The last node should be the root (addition)
        let root = nodes.last().unwrap();
        assert_eq!(root.children().len(), 2);

        // In a correct postorder traversal:
        // 1. All children of a node must appear before the node itself
        for (i, node) in nodes.iter().enumerate() {
            let children = node.children();
            for child in children {
                // Find where this child appears in our traversal
                if let Some(child_pos) = nodes[0..i].iter().position(|n| n == &child) {
                    // Child should appear before parent (position < i)
                    assert!(
                        child_pos < i,
                        "Child at position {} should appear before parent at position {}",
                        child_pos,
                        i
                    );
                } else {
                    // If child isn't in our traversal list at all, that's an error
                    panic!("Child not found in traversal list");
                }
            }
        }

        Ok(())
    }
}
