//! Filtered iterator for AST nodes.

use crate::prelude::*;

/// An iterator that filters nodes from another iterator based on a predicate.
///
/// This is useful for focusing on specific node types or skipping certain subtrees.
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
/// // Create a filtered iterator that only yields BitVec nodes
/// let iter = FilteredIter::new(
///     PostOrderIter::from(var_ast),
///     |node| matches!(node, DynAst::BitVec(_))
/// );
///
/// // Collect only BitVec nodes
/// let bitvec_nodes: Vec<DynAst> = iter.collect();
/// ```
pub struct FilteredIter<'c, I, F>
where
    I: Iterator<Item = DynAst<'c>>,
    F: FnMut(&DynAst<'c>) -> bool,
{
    /// The underlying iterator
    inner: I,
    /// The predicate function
    predicate: F,
}

impl<'c, I, F> FilteredIter<'c, I, F>
where
    I: Iterator<Item = DynAst<'c>>,
    F: FnMut(&DynAst<'c>) -> bool,
{
    /// Creates a new filtered iterator from another iterator and a predicate.
    pub fn new(inner: I, predicate: F) -> Self {
        FilteredIter { inner, predicate }
    }
}

impl<'c, I, F> Iterator for FilteredIter<'c, I, F>
where
    I: Iterator<Item = DynAst<'c>>,
    F: FnMut(&DynAst<'c>) -> bool,
{
    type Item = DynAst<'c>;

    fn next(&mut self) -> Option<Self::Item> {
        // Keep getting nodes from the inner iterator until we find one that matches the predicate
        self.inner.by_ref().find(|node| (self.predicate)(node))
    }
}

#[cfg(test)]
mod tests {
    use super::super::postorder::PostOrderIter;
    use super::*;

    #[test]
    fn test_filtered_iter() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        // Create a simple AST: (a + (b * c))
        let a = ctx.bvs("a", 64)?;
        let b = ctx.bvs("b", 64)?;
        let c = ctx.bvs("c", 64)?;
        let b_mul_c = ctx.mul(&b, &c)?;
        let a_add_bc = ctx.add(&a, &b_mul_c)?;

        let var_ast = DynAst::from(&a_add_bc);

        // Create a filtered iterator that only yields BitVec nodes
        let bitvec_nodes: Vec<DynAst> =
            FilteredIter::new(PostOrderIter::from(var_ast.clone()), |node| {
                matches!(node, DynAst::BitVec(_))
            })
            .collect();

        // All nodes in our example are BitVec nodes, so we should have 5 nodes
        assert_eq!(bitvec_nodes.len(), 5);

        // Create a filtered iterator that only yields leaf nodes
        let leaf_nodes: Vec<DynAst> = FilteredIter::new(PostOrderIter::from(var_ast), |node| {
            node.children().is_empty()
        })
        .collect();

        // We should have 3 leaf nodes (a, b, c)
        assert_eq!(leaf_nodes.len(), 3);

        // All nodes should be leaves (have no children)
        for node in &leaf_nodes {
            assert!(
                node.children().is_empty(),
                "Node should be a leaf (have no children)"
            );
        }

        Ok(())
    }
}
