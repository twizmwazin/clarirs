use std::{
    collections::BTreeSet,
    fmt::Debug,
    hash::{Hash, Hasher},
    sync::{Arc, atomic::AtomicU64},
};

use crate::{
    ast::op::{AstOp, AstOpChildIter, AstType},
    context::structural_hash,
    prelude::*,
};

/// A node in an AST. A single node type serves every sort; the node caches its
/// [`AstType`] so its sort can be queried in O(1) without inspecting the operation.
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
    /// The set of variable names appearing in this node's subtree. Shared behind
    /// an `Arc` so that re-annotating a node (which leaves the op, and hence the
    /// variables, unchanged) can reuse it instead of recollecting and
    /// reallocating the whole set.
    #[serde(skip)]
    variables: Arc<BTreeSet<InternedString>>,
    #[serde(skip)]
    depth: u32,
    #[serde(skip)]
    symbolic: bool,
    #[serde(skip)]
    simplifiable: bool,
    /// Hash of this node's simplified form (`0` = none), resolved via the AST cache.
    #[serde(skip)]
    pub(crate) simplified: AtomicU64,
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

impl Eq for AstNode<'_> {}

impl<'c> HasContext<'c> for AstNode<'c> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c> AstNode<'c> {
    /// Build a node, deriving its cached metadata including the structural hash.
    pub(crate) fn new(
        ctx: &'c Context<'c>,
        op: AstOp<'c>,
        annotations: BTreeSet<Annotation>,
        ast_type: AstType,
    ) -> Self {
        let variables = Arc::new(op.variables());
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

        let hash = structural_hash(ast_type, &op, &annotations);

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
            simplified: AtomicU64::new(0),
        }
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
        // Mirror `make_ast_annotated`: keep our own annotations, add the new
        // ones, and fold in the relocatable annotations of our children. The op
        // is unchanged, so go through the metadata-reusing fast path rather than
        // rebuilding the node (and its variable set) from scratch.
        let mut combined: BTreeSet<Annotation> = self
            .annotations()
            .iter()
            .cloned()
            .chain(annotations)
            .collect();
        combined.extend(
            self.op
                .child_iter()
                .flat_map(|c| c.annotations().clone())
                .filter(|a| a.relocatable()),
        );
        self.with_annotations(combined)
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

    /// The shared handle to this node's variable set. Exposed for callers that
    /// want to share the set rather than clone its contents.
    pub(crate) fn variables_arc(&self) -> &Arc<BTreeSet<InternedString>> {
        &self.variables
    }

    /// Re-intern this node's op under a new set of annotations, reusing the
    /// op-derived metadata (variables, depth, symbolic, type) rather than
    /// recomputing it.
    ///
    /// Annotations do not affect which variables a node contains, how deep it is,
    /// or whether it is symbolic — only the op and its children do, and those are
    /// unchanged here. So the (potentially large) variable set is shared via its
    /// `Arc` instead of being recollected and reallocated, and only the
    /// annotation-dependent fields (`simplifiable` and the structural hash) are
    /// recomputed. This is the fast path behind all annotation edits.
    pub fn with_annotations(
        &self,
        annotations: BTreeSet<Annotation>,
    ) -> Result<Arc<Self>, ClarirsError> {
        let symbolic = self.symbolic;
        let simplifiable = (symbolic
            || !annotations
                .iter()
                .any(|a| !a.eliminatable() && !a.relocatable()))
            && self.op.child_iter().all(|c| c.simplifiable());

        let hash = structural_hash(self.ast_type, &self.op, &annotations);

        self.ctx.intern_ast(Self {
            op: self.op.clone(),
            ctx: self.ctx,
            hash,
            ast_type: self.ast_type,
            variables: self.variables.clone(),
            depth: self.depth,
            annotations,
            symbolic,
            simplifiable,
            simplified: AtomicU64::new(0),
        })
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
    use std::collections::BTreeSet;
    use std::sync::Arc;

    use crate::ast::annotation::{Annotation, AnnotationType};
    use crate::prelude::*;

    fn sample_annotation() -> Annotation {
        Annotation::new(AnnotationType::Uninitialized, true, true)
    }

    /// Re-annotating a node must preserve all of its op-derived metadata, since
    /// annotations do not change which variables a node has, how deep it is, or
    /// whether it is symbolic.
    #[test]
    fn with_annotations_preserves_metadata() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32)?;
        let y = ctx.bvs("y", 32)?;
        let expr = ctx.add(&x, &y)?;

        let annotated = expr.with_annotations(BTreeSet::from([sample_annotation()]))?;

        assert_eq!(annotated.variables(), expr.variables());
        assert_eq!(annotated.depth(), expr.depth());
        assert_eq!(annotated.symbolic(), expr.symbolic());
        assert_eq!(annotated.ast_type(), expr.ast_type());
        assert_eq!(annotated.op(), expr.op());
        assert_eq!(annotated.annotations().len(), 1);
        Ok(())
    }

    /// The whole point of the fast path: the variable set is shared, not
    /// recollected and reallocated, when only annotations change.
    #[test]
    fn with_annotations_shares_variable_set() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32)?;
        let y = ctx.bvs("y", 32)?;
        let expr = ctx.add(&x, &y)?;

        let annotated = expr.with_annotations(BTreeSet::from([sample_annotation()]))?;

        // The two nodes must hand out pointer-equal variable sets: re-annotation
        // clones the `Arc`, it does not build a new `BTreeSet`.
        assert!(Arc::ptr_eq(expr.variables_arc(), annotated.variables_arc()));
        Ok(())
    }

    /// Going through the public `annotate` helper should also keep variables
    /// consistent and accumulate annotations.
    #[test]
    fn annotate_accumulates_and_preserves_variables() -> Result<(), ClarirsError> {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32)?;
        let expr = ctx.add(&x, &x)?;

        let once = expr.clone().annotate([sample_annotation()])?;
        assert_eq!(once.variables(), expr.variables());
        assert!(once.variables().contains("x"));
        Ok(())
    }
}
