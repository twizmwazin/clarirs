//! Pre-order traversal iterator for AST nodes.

use ahash::{HashSet, HashSetExt};

use super::AstIterator;
use crate::prelude::*;

/// An iterator that traverses an AST in pre-order (parent first, then children).
///
/// This is useful for operations that need to process parents before children,
/// such as structural copying or pattern matching from the root down.
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
/// // Create an iterator that traverses the AST in pre-order
/// let iter = PreOrderIter::from(var_ast);
///
/// // Collect nodes in pre-order
/// let nodes: Vec<DynAst> = iter.collect();
/// ```
pub struct PreOrderIter<'c> {
    /// Stack of nodes to visit
    stack: Vec<DynAst<'c>>,
    /// Set of nodes that have been visited to handle cycles
    visited: HashSet<DynAst<'c>>,
}

impl<'c> PreOrderIter<'c> {
    /// Creates a new pre-order iterator from an AST node.
    pub fn new(ast: DynAst<'c>) -> Self {
        Self::from_ast(ast)
    }
}

impl<'c> AstIterator<'c> for PreOrderIter<'c> {
    fn from_ast(ast: DynAst<'c>) -> Self {
        let mut iter = PreOrderIter {
            stack: Vec::new(),
            visited: HashSet::new(),
        };

        // Push the initial node onto the stack
        iter.stack.push(ast);

        iter
    }
}

impl<'c> From<DynAst<'c>> for PreOrderIter<'c> {
    fn from(value: DynAst<'c>) -> Self {
        Self::from_ast(value)
    }
}

impl<'c> Iterator for PreOrderIter<'c> {
    type Item = DynAst<'c>;

    fn next(&mut self) -> Option<Self::Item> {
        // Pop the next node from the stack
        let node = self.stack.pop()?;

        // Skip if we've already visited this node (handles cycles)
        if !self.visited.insert(node.clone()) {
            return self.next();
        }

        // Push children onto the stack in reverse order
        // so they'll be processed in the correct order
        let children = node.children();
        for child in children.into_iter().rev() {
            if !self.visited.contains(&child) {
                self.stack.push(child);
            }
        }

        // Return the node
        Some(node)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_preorder() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Create a simple AST: (a + (b * c))
        let a = ctx.bvs("a", 64)?;
        let b = ctx.bvs("b", 64)?;
        let c = ctx.bvs("c", 64)?;
        let b_mul_c = ctx.mul(&b, &c)?;
        let a_add_bc = ctx.add(&a, &b_mul_c)?;

        let var_ast = DynAst::from(&a_add_bc);

        // Collect nodes in preorder
        let nodes: Vec<DynAst> = PreOrderIter::from_ast(var_ast).collect();

        // We should have 5 nodes in total (a+(b*c), a, b*c, b, c)
        assert_eq!(nodes.len(), 5);

        // Simple test: The first node should be the root (addition)
        let root = &nodes[0];
        assert_eq!(root.children().len(), 2);

        // In a correct preorder traversal:
        // 1. A parent node must appear before all of its children
        for (i, node) in nodes.iter().enumerate() {
            let children = node.children();
            for child in children {
                // Find where this child appears in our traversal
                if let Some(child_pos) = nodes.iter().position(|n| n == &child) {
                    // Child should appear after parent (position > i)
                    assert!(
                        child_pos > i,
                        "Child at position {} should appear after parent at position {}",
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
