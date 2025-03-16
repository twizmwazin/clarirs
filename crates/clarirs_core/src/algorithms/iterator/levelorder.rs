//! Level-order (breadth-first) traversal iterator for AST nodes.

use ahash::{HashSet, HashSetExt};
use std::collections::VecDeque;

use super::AstIterator;
use crate::prelude::*;

/// An iterator that traverses an AST in level-order (breadth-first).
///
/// This traversal visits nodes level by level, from top to bottom.
/// It's useful for finding the shortest path to nodes with certain properties
/// or analyzing AST structure by depth.
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
/// // Create an iterator that traverses the AST in level-order
/// let iter = LevelOrderIter::from(var_ast);
///
/// // Collect nodes in level-order
/// let nodes: Vec<DynAst> = iter.collect();
/// ```
pub struct LevelOrderIter<'c> {
    /// Queue of nodes to visit
    queue: VecDeque<DynAst<'c>>,
    /// Set of nodes that have been visited to handle cycles
    visited: HashSet<DynAst<'c>>,
}

impl<'c> LevelOrderIter<'c> {
    /// Creates a new level-order iterator from an AST node.
    pub fn new(ast: DynAst<'c>) -> Self {
        Self::from_ast(ast)
    }
}

impl<'c> AstIterator<'c> for LevelOrderIter<'c> {
    fn from_ast(ast: DynAst<'c>) -> Self {
        let mut iter = LevelOrderIter {
            queue: VecDeque::new(),
            visited: HashSet::new(),
        };

        // Enqueue the initial node
        iter.queue.push_back(ast);

        iter
    }
}

impl<'c> From<DynAst<'c>> for LevelOrderIter<'c> {
    fn from(value: DynAst<'c>) -> Self {
        Self::from_ast(value)
    }
}

impl<'c> Iterator for LevelOrderIter<'c> {
    type Item = DynAst<'c>;

    fn next(&mut self) -> Option<Self::Item> {
        // Dequeue the next node
        let node = self.queue.pop_front()?;

        // Skip if we've already visited this node (handles cycles)
        if !self.visited.insert(node.clone()) {
            return self.next();
        }

        // Enqueue all children
        for child in node.children() {
            if !self.visited.contains(&child) {
                self.queue.push_back(child);
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
    fn test_levelorder() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Create a simple AST: (a + (b * c))
        let a = ctx.bvs("a", 64)?;
        let b = ctx.bvs("b", 64)?;
        let c = ctx.bvs("c", 64)?;
        let b_mul_c = ctx.mul(&b, &c)?;
        let a_add_bc = ctx.add(&a, &b_mul_c)?;

        let var_ast = DynAst::from(&a_add_bc);

        // Collect nodes in level-order
        let nodes: Vec<DynAst> = LevelOrderIter::from_ast(var_ast).collect();

        // We should have 5 nodes in total
        assert_eq!(nodes.len(), 5);

        // Simple test: The first node should be the root (addition)
        let root = &nodes[0];
        assert_eq!(root.children().len(), 2);

        // In a level-order traversal:
        // 1. All nodes at depth d appear before any node at depth d+1
        // 2. A parent node must appear before all of its children

        // Check that parents appear before their children
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

        // For our simple AST, we can also check the exact order:
        // Level 0: a+(b*c)
        // Level 1: a, b*c
        // Level 2: b, c

        // The first node should be the root
        assert_eq!(nodes[0].children().len(), 2);

        // The next two nodes should be the direct children of the root
        let root_children = nodes[0].children();
        assert!(
            root_children.contains(&nodes[1]) && root_children.contains(&nodes[2]),
            "Nodes at positions 1 and 2 should be the direct children of the root"
        );

        // If nodes[2] is the multiplication node, its children should be the last two nodes
        if nodes[2].children().len() == 2 {
            let mul_children = nodes[2].children();
            assert!(
                mul_children.contains(&nodes[3]) && mul_children.contains(&nodes[4]),
                "Nodes at positions 3 and 4 should be the children of the multiplication node"
            );
        }

        Ok(())
    }
}
