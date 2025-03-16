//! Leaf node iterator for AST nodes.

use super::AstIterator;
use super::filtered::FilteredIter;
use super::preorder::PreOrderIter;
use crate::prelude::*;

/// An iterator that yields only leaf nodes (nodes with no children) from an AST.
///
/// This is useful for collecting all variables or constants in an expression,
/// or focusing on terminal elements of the AST.
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
/// // Create an iterator that yields only leaf nodes
/// let iter = LeafIter::from(var_ast);
///
/// // Collect leaf nodes
/// let leaves: Vec<DynAst> = iter.collect();
/// // Should contain only the variables a, b, and c
/// assert_eq!(leaves.len(), 3);
/// ```
pub struct LeafIter<'c> {
    /// The underlying filtered iterator
    inner: FilteredIter<'c, PreOrderIter<'c>, fn(&DynAst<'c>) -> bool>,
}

impl<'c> LeafIter<'c> {
    /// Creates a new leaf iterator from an AST node.
    pub fn new(ast: DynAst<'c>) -> Self {
        Self::from_ast(ast)
    }
}

impl<'c> AstIterator<'c> for LeafIter<'c> {
    fn from_ast(ast: DynAst<'c>) -> Self {
        LeafIter {
            inner: FilteredIter::new(PreOrderIter::from_ast(ast), |node| {
                node.child_iter().len() == 0
            }),
        }
    }
}

impl<'c> From<DynAst<'c>> for LeafIter<'c> {
    fn from(value: DynAst<'c>) -> Self {
        Self::from_ast(value)
    }
}

impl<'c> Iterator for LeafIter<'c> {
    type Item = DynAst<'c>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leaf_iter() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Create a simple AST: (a + (b * c))
        let a = ctx.bvs("a", 64)?;
        let b = ctx.bvs("b", 64)?;
        let c = ctx.bvs("c", 64)?;
        let b_mul_c = ctx.mul(&b, &c)?;
        let a_add_bc = ctx.add(&a, &b_mul_c)?;

        let var_ast = DynAst::from(&a_add_bc);

        // Collect leaf nodes
        let leaves: Vec<DynAst> = LeafIter::from_ast(var_ast).collect();

        // We should have 3 leaf nodes (a, b, c)
        assert_eq!(leaves.len(), 3);

        // All nodes should be leaves (have no children)
        for node in &leaves {
            assert!(
                node.children().is_empty(),
                "Node should be a leaf (have no children)"
            );
        }

        // The leaves should include all variables
        let a_ast = DynAst::from(&a);
        let b_ast = DynAst::from(&b);
        let c_ast = DynAst::from(&c);

        assert!(
            leaves.contains(&a_ast) && leaves.contains(&b_ast) && leaves.contains(&c_ast),
            "Leaves should include all variables"
        );

        Ok(())
    }
}
