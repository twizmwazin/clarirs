use std::{
    collections::BTreeSet,
    fmt::Debug,
    hash::{Hash, Hasher},
    sync::Arc,
    sync::atomic::{AtomicU64, Ordering},
};

use crate::{
    ast::op::{AstOp, AstOpChildIter, AstType},
    cache::AstCache,
    prelude::*,
};

/// A node in an AST. A single node type serves every sort; the node caches its
/// [`AstType`] so its sort can be queried in O(1) without inspecting the operation.
///
/// This node's excavated form is memoized inline in [`AstNode::excavation_cache`],
/// which holds the result node's hash (resolved back through the interning table).
#[derive(serde::Serialize)]
pub struct AstNode<'c> {
    op: AstOp<'c>,
    annotations: BTreeSet<Annotation>,
    #[serde(skip)]
    ast_type: AstType,
    #[serde(skip)]
    ctx: &'c Context<'c>,
    #[serde(skip)]
    hash: u64,
    #[serde(skip)]
    variables: BTreeSet<InternedString>,
    #[serde(skip)]
    depth: u32,
    #[serde(skip)]
    symbolic: bool,
    #[serde(skip)]
    simplifiable: bool,
    /// Hash of this node's ITE-excavated form, or 0 if uncomputed. A stale hash
    /// (result dropped) just misses and recomputes, hence overwritable.
    #[serde(skip)]
    excavation_cache: AtomicU64,
}

impl Drop for AstNode<'_> {
    fn drop(&mut self) {
        self.ctx.drop_cache(self.hash);
    }
}

impl Debug for AstNode<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AstNode").field("op", &self.op).finish()
    }
}

impl Hash for AstNode<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}

impl PartialEq for AstNode<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.op == other.op && self.annotations == other.annotations
    }
}

// Structural equality (op + annotations); the inline caches are excluded.
impl Eq for AstNode<'_> {}

impl<'c> HasContext<'c> for AstNode<'c> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c> AstNode<'c> {
    pub(crate) fn new(
        ctx: &'c Context<'c>,
        op: AstOp<'c>,
        annotations: BTreeSet<Annotation>,
        hash: u64,
        ast_type: AstType,
    ) -> Self {
        let variables = op.variables();
        let depth = 1 + op.child_iter().map(|c| c.depth()).max().unwrap_or(0);
        // Symbolic propagates from: having variables, the op itself being inherently
        // symbolic (e.g. VSA Union/Intersection/Widen), or any child being symbolic.
        let symbolic = !variables.is_empty()
            || op.is_inherently_symbolic()
            || op.child_iter().any(|c| c.symbolic());

        let simplifiable = (symbolic
            || !annotations
                .iter()
                .any(|a| !a.eliminatable() && !a.relocatable()))
            && op.child_iter().all(|c| c.simplifiable());

        Self {
            op,
            ctx,
            hash,
            ast_type,
            variables,
            depth,
            annotations,
            symbolic,
            simplifiable,
            excavation_cache: AtomicU64::new(0),
        }
    }

    /// Resolve a result cell's stored hash to a live node, or `None` if unset (0)
    /// or stale.
    fn cached(&self, cell: &AtomicU64) -> Option<AstRef<'c>> {
        match cell.load(Ordering::Relaxed) {
            0 => None,
            hash => self.ctx.ast_cache.get(hash),
        }
    }

    /// This node's memoized ITE-excavated form, if still live.
    pub(crate) fn cached_excavated(&self) -> Option<AstRef<'c>> {
        self.cached(&self.excavation_cache)
    }

    pub(crate) fn set_cached_excavated(&self, node: &AstRef<'c>) {
        self.excavation_cache.store(node.hash, Ordering::Relaxed);
    }

    pub fn simplifiable(&self) -> bool {
        self.simplifiable
    }

    pub fn op(&self) -> &AstOp<'c> {
        &self.op
    }

    pub fn ast_type(&self) -> AstType {
        self.ast_type
    }

    pub fn annotations(&self) -> &BTreeSet<Annotation> {
        &self.annotations
    }

    pub fn annotate(
        self: Arc<Self>,
        annotations: impl IntoIterator<Item = Annotation>,
    ) -> Result<Arc<Self>, ClarirsError> {
        let combined = self
            .annotations()
            .iter()
            .cloned()
            .chain(annotations)
            .collect();
        self.context().make_ast_annotated(self.op.clone(), combined)
    }

    pub fn hash(&self) -> u64 {
        self.hash
    }

    pub fn symbolic(&self) -> bool {
        self.symbolic
    }

    pub fn concrete(&self) -> bool {
        !self.symbolic
    }

    pub fn variables(&self) -> &BTreeSet<InternedString> {
        &self.variables
    }

    pub fn size(&self) -> u32 {
        match self.ast_type {
            AstType::BitVec(width) => width,
            AstType::Float(sort) => sort.size(),
            AstType::Bool | AstType::String => 0,
        }
    }

    /// The float sort of this node. For non-float nodes this falls back to a
    /// default and should not be relied upon; check [`AstType::is_float`] first.
    pub fn sort(&self) -> FSort {
        if let AstType::Float(sort) = self.ast_type {
            sort
        } else {
            FSort::f64()
        }
    }

    /// Chop a bitvector into `bits`-sized pieces, returned in little-endian order.
    pub fn chop(self: &Arc<Self>, bits: u32) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        if !self.size().is_multiple_of(bits) {
            return Err(ClarirsError::InvalidChopSize {
                size: self.size(),
                bits,
            });
        }
        let mut res = vec![];
        for i in 0..self.size() / bits {
            res.push(
                self.context()
                    .extract(self, ((i + 1) * bits) - 1, i * bits)?,
            );
        }
        res.reverse();
        Ok(res)
    }

    pub fn depth(&self) -> u32 {
        self.depth
    }

    pub fn child_iter(&self) -> AstOpChildIter<'_, 'c> {
        self.op.child_iter()
    }

    pub fn get_child(&self, index: usize) -> Option<AstRef<'c>> {
        self.op.get_child(index)
    }

    pub fn is_leaf(&self) -> bool {
        self.op.num_children() == 0
    }

    pub fn is_true(&self) -> bool {
        self.op.is_true()
    }

    pub fn is_false(&self) -> bool {
        self.op.is_false()
    }

    /// Returns true if both nodes have the same sort (type and size).
    pub fn check_same_sort(&self, other: &Self) -> bool {
        self.ast_type == other.ast_type
    }

    // Runtime-checked accessors: each returns the node back only if its cached
    // type tag matches, for validating ASTs that cross an API boundary.

    pub fn into_bool(self: Arc<Self>) -> Option<Arc<Self>> {
        self.ast_type.is_bool().then_some(self)
    }

    pub fn into_bitvec(self: Arc<Self>) -> Option<Arc<Self>> {
        self.ast_type.is_bitvec().then_some(self)
    }

    pub fn into_float(self: Arc<Self>) -> Option<Arc<Self>> {
        self.ast_type.is_float().then_some(self)
    }

    pub fn into_string(self: Arc<Self>) -> Option<Arc<Self>> {
        self.ast_type.is_string().then_some(self)
    }
}

/// A reference-counted handle to an [`AstNode`]. This is the single, universal
/// AST type for every sort; the node's cached [`AstType`] distinguishes sorts
/// at runtime.
pub type AstRef<'c> = Arc<AstNode<'c>>;

pub trait IntoOwned<T> {
    fn into_owned(self) -> T;
}

impl<T> IntoOwned<T> for T {
    fn into_owned(self) -> T {
        self
    }
}

impl<T: Clone> IntoOwned<T> for &T {
    fn into_owned(self) -> T {
        self.clone()
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;

    /// Excavating populates the node's inline cell with its excavated form, and
    /// resolving the cell yields that same interned node.
    ///
    /// Cells resolve through the interning table, which under
    /// `panic-on-hash-collision` deliberately rebuilds and re-inserts a fresh
    /// (immediately-dead) duplicate on every construction, so cells degrade to
    /// always-miss there. The behavior under test only holds without that mode.
    #[cfg(not(feature = "panic-on-hash-collision"))]
    #[test]
    fn excavated_memoized_inline() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 64)?;
        let one = ctx.bvv(BitVec::from((1u64, 64)))?;
        let expr = ctx.add(&x, &one)?;

        // Cold: nothing memoized yet.
        assert!(expr.cached_excavated().is_none());

        let excavated = expr.excavate_ite()?;

        // The cell now resolves to the excavated node without recomputation.
        assert_eq!(expr.cached_excavated(), Some(excavated));
        Ok(())
    }

    /// A cell whose stored result has been garbage-collected resolves to `None`
    /// (a miss → recompute) rather than a stale or dangling reference. The
    /// result is interned under a weak reference, so once no strong handle
    /// remains the cell misses.
    #[cfg(not(feature = "panic-on-hash-collision"))]
    #[test]
    fn stale_cell_misses_after_result_dropped() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        // `a + ite(c, x, y)` excavates to the *fresh* node `ite(c, a + x, a + y)`,
        // which is not a sub-expression of the source, so the source does not
        // keep it alive.
        let a = ctx.bvs("a", 64)?;
        let x = ctx.bvs("x", 64)?;
        let y = ctx.bvs("y", 64)?;
        let c = ctx.bools("c")?;
        let ite = ctx.ite(&c, &x, &y)?;
        let expr = ctx.add(&a, &ite)?;

        let excavated = expr.excavate_ite()?;
        assert!(expr.cached_excavated().is_some());

        // Drop every strong handle to the excavated result.
        drop(excavated);

        // The interning table held only a weak ref, so the cell now misses.
        assert!(expr.cached_excavated().is_none());
        Ok(())
    }
}
