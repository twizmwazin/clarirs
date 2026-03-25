use std::{
    collections::BTreeSet,
    fmt::Debug,
    hash::{Hash, Hasher},
    sync::Arc,
};

use crate::prelude::*;

#[derive(Clone, Eq, serde::Serialize)]
pub struct AstNode<'c> {
    op: Op<'c>,
    return_type: AstType,
    annotations: BTreeSet<Annotation>,
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
}

impl<'c> Drop for AstNode<'c> {
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

impl<'c> HasContext<'c> for AstNode<'c> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c> AstNode<'c> {
    pub(crate) fn new(
        ctx: &'c Context<'c>,
        op: Op<'c>,
        annotations: BTreeSet<Annotation>,
        hash: u64,
    ) -> Self {
        let return_type = op.return_type();
        let variables = op.variables();
        let depth = op.depth();
        // If we have variables, we're symbolic. Also check is_inherently_symbolic
        // for VSA ops that are symbolic even without variables. No need to check
        // children separately — their variables are already included in ours.
        let symbolic = !variables.is_empty() || op.is_inherently_symbolic();

        Self {
            op,
            return_type,
            ctx,
            hash,
            variables,
            depth,
            annotations,
            symbolic,
        }
    }

    pub fn op(&self) -> &Op<'c> {
        &self.op
    }

    pub fn return_type(&self) -> AstType {
        self.return_type
    }

    pub fn annotations(&self) -> &BTreeSet<Annotation> {
        &self.annotations
    }

    pub fn annotate(
        self: Arc<Self>,
        annotations: impl IntoIterator<Item = Annotation>,
    ) -> Result<Arc<Self>, ClarirsError> {
        self.context().annotate(&self, annotations)
    }

    pub fn hash(&self) -> u64 {
        self.hash
    }

    pub fn symbolic(&self) -> bool {
        self.symbolic
    }

    pub fn variables(&self) -> &BTreeSet<InternedString> {
        &self.variables
    }

    pub fn depth(&self) -> u32 {
        self.depth
    }

    pub fn size(&self) -> u32 {
        self.return_type.size()
    }

    pub fn sort(&self) -> Option<FSort> {
        self.return_type.sort()
    }

    pub fn is_true(&self) -> bool {
        self.op.is_true()
    }

    pub fn is_false(&self) -> bool {
        self.op.is_false()
    }

    pub fn concrete(&self) -> bool {
        !self.symbolic
    }

    pub fn child_iter(&self) -> OpChildIter<'_, 'c> {
        self.op.child_iter()
    }

    pub fn get_child(&self, index: usize) -> Option<AstRef<'c>> {
        self.op.get_child(index)
    }

    pub fn check_same_sort(&self, other: &Self) -> bool {
        self.return_type == other.return_type
    }

    /// Chop a BitVec AST into `bits` sized pieces. Returns in little-endian order.
    pub fn chop(self: &Arc<Self>, bits: u32) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        let size = self.size();
        if size % bits != 0 {
            return Err(ClarirsError::InvalidChopSize { size, bits });
        }
        let mut res = vec![];
        for i in 0..size / bits {
            res.push(self.context().extract(self, ((i + 1) * bits) - 1, i * bits)?);
        }
        res.reverse();
        Ok(res)
    }
}

/// The primary AST reference type — a reference-counted pointer to an AstNode.
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
