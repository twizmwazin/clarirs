//! Transformation iterator for AST nodes.

use ahash::{HashSet, HashSetExt};

use super::{AstIterator, PostOrderIter};
use crate::prelude::*;

/// An iterator that applies a transformation function to each node in an AST.
///
/// This iterator traverses the AST in post-order (children first, then parent)
/// and applies a transformation function to each node. It tracks which nodes have
/// already been transformed to avoid re-running transformations on duplicate nodes.
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
/// // Create a transformation function
/// let transform = |node: DynAst| -> Result<DynAst, ClarirsError> {
///     // For example, simplify constants
///     if node.children().is_empty() {
///         // This is a leaf node, return as is
///         Ok(node)
///     } else {
///         // For non-leaf nodes, we could apply some transformation
///         // Here we just return the node unchanged
///         Ok(node)
///     }
/// };
///
/// // Create a transform iterator
/// let iter = TransformIter::new(var_ast, transform);
///
/// // Collect transformed nodes
/// let transformed_nodes: Vec<DynAst> = iter.collect();
/// ```
pub struct TransformIter<'c, F>
where
    F: FnMut(DynAst<'c>) -> Result<DynAst<'c>, ClarirsError>,
{
    /// The underlying post-order iterator
    inner: PostOrderIter<'c>,
    /// The transformation function
    transform: F,
    /// Set of nodes that have already been transformed
    transformed: HashSet<DynAst<'c>>,
    /// Whether an error has been encountered
    has_error: bool,
}

impl<'c, F> TransformIter<'c, F>
where
    F: FnMut(DynAst<'c>) -> Result<DynAst<'c>, ClarirsError>,
{
    /// Creates a new transformation iterator from an AST node and a transformation function.
    pub fn new(ast: DynAst<'c>, transform: F) -> Self {
        Self {
            inner: PostOrderIter::from_ast(ast),
            transform,
            transformed: HashSet::new(),
            has_error: false,
        }
    }
}

impl<'c, F> Iterator for TransformIter<'c, F>
where
    F: FnMut(DynAst<'c>) -> Result<DynAst<'c>, ClarirsError>,
{
    type Item = DynAst<'c>;

    fn next(&mut self) -> Option<Self::Item> {
        // If we've encountered an error, return None to stop iteration
        if self.has_error {
            return None;
        }

        // Get the next node from the inner iterator
        for node in self.inner.by_ref() {
            // Check if we've already transformed this node
            if self.transformed.contains(&node) {
                continue;
            }

            // Apply the transformation
            match (self.transform)(node.clone()) {
                Ok(transformed) => {
                    // Mark this node as transformed
                    self.transformed.insert(node);
                    return Some(transformed);
                }
                Err(_) => {
                    // Mark that we've encountered an error and stop iteration
                    self.has_error = true;
                    return None;
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
    fn test_transform_iter() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Create a simple AST: (a + (b * c))
        let a = ctx.bvs("a", 64)?;
        let b = ctx.bvs("b", 64)?;
        let c = ctx.bvs("c", 64)?;
        let b_mul_c = ctx.mul(&b, &c)?;
        let a_add_bc = ctx.add(&a, &b_mul_c)?;

        let var_ast = DynAst::from(&a_add_bc);

        // Create a transform iterator that just returns nodes unchanged
        let transformed_nodes: Vec<DynAst> = TransformIter::new(var_ast.clone(), Ok).collect();

        // We should have 5 nodes in total (a, b, c, b*c, a+(b*c))
        assert_eq!(transformed_nodes.len(), 5);

        // Test with duplicate nodes
        let dup_a = ctx.bvs("a", 64)?; // Same as 'a' above
        let dup_ast = ctx.add(&dup_a, &a_add_bc)?;
        let var_dup_ast = DynAst::from(&dup_ast);

        // Create a transform iterator
        let transformed_nodes: Vec<DynAst> = TransformIter::new(var_dup_ast, Ok).collect();

        // We should have 6 nodes in total (a, b, c, b*c, a+(b*c), a+(a+(b*c)))
        // Note: 'a' appears twice in the AST but should only be transformed once
        assert_eq!(transformed_nodes.len(), 6);

        // Test error propagation
        let error_transform = |_: DynAst| -> Result<DynAst, ClarirsError> {
            Err(ClarirsError::UnsupportedOperation("Test error".to_string()))
        };

        let transformed_nodes: Vec<DynAst> = TransformIter::new(var_ast, error_transform).collect();
        // The iterator should stop at the first error, so we should have an empty vector
        assert_eq!(transformed_nodes.len(), 0);

        Ok(())
    }

    #[test]
    fn test_boolean_constant_folding() -> Result<(), ClarirsError> {
        let ctx: Context = Context::new();

        // Create a boolean AST with constants: (true && (false || true))
        let true_val = ctx.true_()?;
        let false_val = ctx.false_()?;
        let or_expr = ctx.or(&false_val, &true_val)?;
        let and_expr = ctx.and(&true_val, &or_expr)?;

        let var_ast = DynAst::from(&and_expr);

        // Create a constant folding transformation
        let transform = |node| {
            if let DynAst::Boolean(ast) = &node {
                match ast.op() {
                    BooleanOp::And(lhs, rhs) => {
                        // Constant folding for AND
                        if lhs.is_true() {
                            // true && x = x
                            Ok(DynAst::from(rhs))
                        } else if lhs.is_false() {
                            // false && x = false
                            Ok(DynAst::from(lhs))
                        } else if rhs.is_true() {
                            // x && true = x
                            Ok(DynAst::from(lhs))
                        } else if rhs.is_false() {
                            // x && false = false
                            Ok(DynAst::from(rhs))
                        } else {
                            // No simplification possible
                            Ok(node)
                        }
                    }
                    BooleanOp::Or(lhs, rhs) => {
                        // Constant folding for OR
                        if lhs.is_true() {
                            // true || x = true
                            Ok(DynAst::from(lhs))
                        } else if lhs.is_false() {
                            // false || x = x
                            Ok(DynAst::from(rhs))
                        } else if rhs.is_true() {
                            // x || true = true
                            Ok(DynAst::from(rhs))
                        } else if rhs.is_false() {
                            // x || false = x
                            Ok(DynAst::from(lhs))
                        } else {
                            // No simplification possible
                            Ok(node)
                        }
                    }
                    _ => Ok(node), // No transformation for other operations
                }
            } else {
                Ok(node) // No transformation for non-boolean nodes
            }
        };

        // Create a transform iterator
        let transformed_nodes: Vec<DynAst> = TransformIter::new(var_ast, transform).collect();

        // The original AST has 4 nodes: true, false, true, (false || true), (true && (false || true))
        // After transformation, we should have simplified nodes
        // The final result should be 'true' since (true && (false || true)) = (true && true) = true

        // Find the root node (last node in post-order traversal)
        if let Some(root) = transformed_nodes.last() {
            if let DynAst::Boolean(ast) = root {
                // The root should be simplified to 'true'
                assert!(
                    ast.is_true(),
                    "Expected root node to be simplified to 'true'"
                );
            } else {
                panic!("Expected root node to be a boolean");
            }
        } else {
            panic!("No nodes in transformed result");
        }

        Ok(())
    }
}
