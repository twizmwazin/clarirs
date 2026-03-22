use std::{
    collections::BTreeSet,
    fmt::Debug,
    hash::{Hash, Hasher},
    sync::Arc,
};

use crate::prelude::*;

#[derive(Clone, Eq, serde::Serialize)]
pub struct AstNode<'c> {
    op: AstOp<'c>,
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
    pub(crate) size: u32,
    #[serde(skip)]
    symbolic: bool,
    #[serde(skip)]
    theories: Theories,
}

impl<'c> Drop for AstNode<'c> {
    fn drop(&mut self) {
        self.ctx.drop_cache(self.hash);
    }
}

impl<'c> Debug for AstNode<'c> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AstNode").field("op", &self.op).finish()
    }
}

impl<'c> Hash for AstNode<'c> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}

impl<'c> PartialEq for AstNode<'c> {
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
        op: AstOp<'c>,
        annotations: BTreeSet<Annotation>,
        hash: u64,
        size: u32,
    ) -> Self {
        let variables = op.variables();
        let depth = op.depth();
        let symbolic = !variables.is_empty()
            || op.is_inherently_symbolic()
            || op.children().any(|c| c.symbolic());
        let theories = op
            .children()
            .fold(op.base_theories(), |acc, c| acc | c.theories());

        Self {
            op,
            ctx,
            hash,
            variables,
            depth,
            size,
            annotations,
            symbolic,
            theories,
        }
    }

    pub fn op(&self) -> &AstOp<'c> {
        &self.op
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

    pub fn size(&self) -> u32 {
        self.size
    }

    pub fn theories(&self) -> Theories {
        self.theories
    }

    pub fn depth(&self) -> u32 {
        self.depth
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

    pub fn get_child(&self, index: usize) -> Option<AstRef<'c>> {
        self.op.get_child(index)
    }

    pub fn child_iter(&self) -> crate::ast::astop::AstOpChildIter<'_, 'c> {
        self.op.children()
    }

    pub fn num_children(&self) -> usize {
        self.op.num_children()
    }
}

impl<'c> HasContext<'c> for Arc<AstNode<'c>> {
    fn context(&self) -> &'c Context<'c> {
        self.as_ref().context()
    }
}
