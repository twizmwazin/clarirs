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
    #[serde(skip)]
    variables: BTreeSet<InternedString>,
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
    /// The node's [`AstType`] is inferred from the operation.
    pub(crate) fn new(
        ctx: &'c Context<'c>,
        op: AstOp<'c>,
        annotations: BTreeSet<Annotation>,
    ) -> Self {
        let ast_type = op.infer_type();
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
        let combined: BTreeSet<_> = self
            .annotations()
            .iter()
            .cloned()
            .chain(annotations)
            .collect();
        let simplifiable = self.simplifiable()
            && !&combined
                .iter()
                .any(|a| !a.eliminatable() && !a.relocatable());

        // Fast path: skip variable collection/allocation in new
        let new_node = Self {
            op: self.op.clone(),
            ctx: self.ctx,
            hash: structural_hash(self.ast_type, &self.op, &combined),
            ast_type: self.ast_type,
            variables: self.variables.clone(),
            depth: self.depth,
            annotations: combined,
            symbolic: self.symbolic,
            simplifiable,
            simplified: AtomicU64::new(0),
        };
        self.context().intern_ast(new_node)
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
    use super::*;
    use crate::util::precomputed_hasher::PrecomputedHasherBuilder;
    use std::hash::BuildHasher;

    #[test]
    fn test_size() {
        let ctx = Context::new();
        assert_eq!(ctx.bvs("x", 32).unwrap().size(), 32);
        assert_eq!(ctx.bvs("y", 1).unwrap().size(), 1);
        assert_eq!(ctx.fps("f", FSort::f64()).unwrap().size(), 64);
        assert_eq!(ctx.fps("g", FSort::f32()).unwrap().size(), 32);
        // Bool and String have no size
        assert_eq!(ctx.bools("b").unwrap().size(), 0);
        assert_eq!(ctx.strings("s").unwrap().size(), 0);
    }

    #[test]
    fn test_sort() {
        let ctx = Context::new();
        assert_eq!(ctx.fps("f", FSort::f32()).unwrap().sort(), FSort::f32());
        assert_eq!(ctx.fps("g", FSort::f64()).unwrap().sort(), FSort::f64());
        // Non-float nodes fall back to f64
        assert_eq!(ctx.bools("b").unwrap().sort(), FSort::f64());
        assert_eq!(ctx.bvs("x", 8).unwrap().sort(), FSort::f64());
    }

    #[test]
    fn test_symbolic_and_concrete() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();
        let v = ctx.bvv(BitVec::from((5, 32))).unwrap();
        assert!(x.symbolic());
        assert!(!x.concrete());
        assert!(v.concrete());
        assert!(!v.symbolic());

        // Symbolic propagates to parents
        let add = ctx.add(&x, &v).unwrap();
        assert!(add.symbolic());

        // VSA ops are inherently symbolic even over concrete children
        let union = ctx.union(&v, &v).unwrap();
        assert!(union.symbolic());
    }

    #[test]
    fn test_variables() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();
        let y = ctx.bvs("y", 32).unwrap();
        let v = ctx.bvv(BitVec::from((5, 32))).unwrap();

        assert!(v.variables().is_empty());

        let x_vars: Vec<&str> = x.variables().iter().map(|s| s.as_str()).collect();
        assert_eq!(x_vars, vec!["x"]);

        let expr = ctx.add(&x, &ctx.add(&y, &v).unwrap()).unwrap();
        let vars: Vec<&str> = expr.variables().iter().map(|s| s.as_str()).collect();
        assert_eq!(vars, vec!["x", "y"]);
    }

    #[test]
    fn test_depth() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();
        let y = ctx.bvs("y", 32).unwrap();
        assert_eq!(x.depth(), 1);
        let add = ctx.add(&x, &y).unwrap();
        assert_eq!(add.depth(), 2);
        let neg = ctx.neg(&add).unwrap();
        assert_eq!(neg.depth(), 3);
    }

    #[test]
    fn test_is_leaf_and_children() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();
        let y = ctx.bvs("y", 32).unwrap();
        let add = ctx.add(&x, &y).unwrap();

        assert!(x.is_leaf());
        assert!(!add.is_leaf());

        assert_eq!(add.get_child(0), Some(x.clone()));
        assert_eq!(add.get_child(1), Some(y.clone()));
        assert_eq!(add.get_child(2), None);

        let children: Vec<AstRef> = add.child_iter().collect();
        assert_eq!(children, vec![x, y]);
    }

    #[test]
    fn test_is_true_is_false() {
        let ctx = Context::new();
        let t = ctx.true_().unwrap();
        let f = ctx.false_().unwrap();
        let b = ctx.bools("b").unwrap();

        assert!(t.is_true());
        assert!(!t.is_false());
        assert!(f.is_false());
        assert!(!f.is_true());
        assert!(!b.is_true());
        assert!(!b.is_false());
    }

    #[test]
    fn test_check_same_sort() {
        let ctx = Context::new();
        let x32 = ctx.bvs("x", 32).unwrap();
        let y32 = ctx.bvs("y", 32).unwrap();
        let z64 = ctx.bvs("z", 64).unwrap();
        let b = ctx.bools("b").unwrap();

        assert!(x32.check_same_sort(&y32));
        assert!(!x32.check_same_sort(&z64));
        assert!(!x32.check_same_sort(&b));
    }

    #[test]
    fn test_into_sort_accessors() {
        let ctx = Context::new();
        let b = ctx.bools("b").unwrap();
        let x = ctx.bvs("x", 32).unwrap();
        let f = ctx.fps("f", FSort::f64()).unwrap();
        let s = ctx.strings("s").unwrap();

        assert!(b.clone().into_bool().is_some());
        assert!(b.clone().into_bitvec().is_none());
        assert!(x.clone().into_bitvec().is_some());
        assert!(x.clone().into_float().is_none());
        assert!(f.clone().into_float().is_some());
        assert!(f.clone().into_string().is_none());
        assert!(s.clone().into_string().is_some());
        assert!(s.clone().into_bool().is_none());
    }

    #[test]
    fn test_chop() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();

        let pieces = x.chop(8).unwrap();
        assert_eq!(pieces.len(), 4);
        // The most-significant chunk comes first (the extract results are
        // reversed before being returned).
        assert_eq!(pieces[0], ctx.extract(&x, 31, 24).unwrap());
        assert_eq!(pieces[1], ctx.extract(&x, 23, 16).unwrap());
        assert_eq!(pieces[2], ctx.extract(&x, 15, 8).unwrap());
        assert_eq!(pieces[3], ctx.extract(&x, 7, 0).unwrap());

        // Chopping into a single piece of the full width works
        let whole = x.chop(32).unwrap();
        assert_eq!(whole.len(), 1);
    }

    #[test]
    fn test_chop_invalid_size() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();
        let err = x.chop(5).unwrap_err();
        assert!(matches!(
            err,
            ClarirsError::InvalidChopSize { size: 32, bits: 5 }
        ));
    }

    #[test]
    fn test_annotate() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();
        assert!(x.annotations().is_empty());

        let ann = Annotation::new(AnnotationType::Uninitialized, true, false);
        let annotated = x.clone().annotate([ann.clone()]).unwrap();

        assert_eq!(annotated.annotations().len(), 1);
        assert!(annotated.annotations().contains(&ann));
        // The op is unchanged, but annotations are part of identity
        assert_eq!(annotated.op(), x.op());
        assert_ne!(annotated, x);
        assert_ne!(annotated.as_ref().hash(), x.as_ref().hash());
    }

    #[test]
    fn test_interning_and_hash() {
        let ctx = Context::new();
        let x1 = ctx.bvs("x", 32).unwrap();
        let x2 = ctx.bvs("x", 32).unwrap();

        // Structurally identical nodes are interned to the same Arc
        assert!(Arc::ptr_eq(&x1, &x2));
        assert_eq!(x1.as_ref().hash(), x2.as_ref().hash());

        // The Hash impl writes only the precomputed hash
        assert_eq!(PrecomputedHasherBuilder.hash_one(&*x1), x1.as_ref().hash());
    }

    #[test]
    fn test_debug_format_shows_op() {
        let ctx = Context::new();
        let t = ctx.true_().unwrap();
        assert_eq!(format!("{t:?}"), "AstNode { op: BoolV(true) }");
    }
}
