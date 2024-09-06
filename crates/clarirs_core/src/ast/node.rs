use std::{
    collections::HashSet,
    fmt::Debug,
    hash::{Hash, Hasher},
    sync::Arc,
};

use serde::Serialize;

use crate::context::{Context, HasContext};

use super::{kind::AstKind, op::AstOp};

#[derive(Clone, Eq, Serialize)]
pub struct AstNode<'c> {
    // Everything can be derived from the op
    op: AstOp<'c>,

    #[serde(skip)]
    ctx: &'c Context<'c>,
    #[serde(skip)]
    kind: AstKind,
    #[serde(skip)]
    hash: u64,
    #[serde(skip)]
    symbolic: bool,
    #[serde(skip)]
    variables: HashSet<String>,
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
        self.hash == other.hash
    }
}

impl<'c> HasContext<'c> for AstNode<'c> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c> AstNode<'c> {
    pub(crate) fn new(ctx: &'c Context<'c>, op: AstOp<'c>, hash: u64) -> Self {
        let kind = op.kind();
        let symbolic = op.child_iter().any(|child| child.symbolic());
        let variables = op
            .child_iter()
            .flat_map(|child| child.variables().iter().cloned())
            .collect();

        Self {
            op,
            ctx,
            kind,
            hash,
            symbolic,
            variables,
        }
    }

    pub fn op(&self) -> &AstOp<'c> {
        &self.op
    }

    pub fn kind(&self) -> AstKind {
        self.kind.clone()
    }

    pub fn hash(&self) -> u64 {
        self.hash
    }

    pub fn symbolic(&self) -> bool {
        self.symbolic
    }

    pub fn variables(&self) -> &HashSet<String> {
        &self.variables
    }

    pub fn child_iter(&self) -> impl Iterator<Item = &AstRef<'c>> {
        self.op.child_iter()
    }

    pub fn children(&self) -> Vec<&AstRef<'c>> {
        self.op.children()
    }

    pub fn is_true(&self) -> bool {
        self.op == AstOp::BoolV(true)
    }

    pub fn is_false(&self) -> bool {
        self.op == AstOp::BoolV(false)
    }
}

pub type AstRef<'c> = Arc<AstNode<'c>>;
