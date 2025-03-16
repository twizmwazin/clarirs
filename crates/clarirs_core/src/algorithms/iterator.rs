//! AST traversal iterators.
//!
//! This module provides various iterators for traversing AST nodes in different orders.

mod filtered;
mod leaf;
mod levelorder;
mod postorder;
mod preorder;
mod transform;

pub use filtered::FilteredIter;
pub use leaf::LeafIter;
pub use levelorder::LevelOrderIter;
pub use postorder::PostOrderIter;
pub use preorder::PreOrderIter;
pub use transform::TransformIter;

use crate::prelude::*;

/// Internal enum to track node states during traversal.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum NodeState {
    /// Node has been discovered but not fully processed
    Discovered,
    /// Node and all its children have been fully processed
    Processed,
}

/// Trait for AST iterators.
///
/// This trait provides a common interface for all AST iterators.
pub trait AstIterator<'c>: Iterator<Item = DynAst<'c>> {
    /// Creates a new iterator from an AST node.
    fn from_ast(ast: DynAst<'c>) -> Self;
}
