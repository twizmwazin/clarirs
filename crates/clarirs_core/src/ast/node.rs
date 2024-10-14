use std::{
    collections::HashSet,
    fmt::Debug,
    hash::{Hash, Hasher},
    sync::Arc,
};

use serde::Serialize;

use crate::context::{Context, HasContext};

use super::kind::AstKind; // op::AstOp

pub trait OpTrait<'c>: Debug + Serialize
where
    Self: Sized,
{
    fn child_iter(&self) -> Box<dyn Iterator<Item = AstRef<'c, Self>> + 'c>;
    fn children(&self) -> Vec<AstRef<'c, Self>> {
        self.child_iter().collect()
    }
    fn is_true(&self) -> bool {
        false
    }
    fn is_false(&self) -> bool {
        false
    }
}

pub trait AstNodeTrait<'c, Op>: Debug + Serialize
where
    Op: OpTrait<'c>,
{
    fn symbolic(&self) -> bool;
    fn variables(&self) -> &HashSet<String>;
    fn child_iter(&self) -> Box<dyn Iterator<Item = AstRef<'c, Op>> + 'c>;
}

#[derive(Clone, Eq, Serialize)]
pub struct AstNode<'c, Op>
where
    Op: OpTrait<'c> + 'c,
{
    op: Op,

    #[serde(skip)]
    ctx: &'c Context<'c>,
    #[serde(skip)]
    hash: u64,
    #[serde(skip)]
    symbolic: bool,
    #[serde(skip)]
    variables: HashSet<String>,
}

impl<'c, Op> Debug for AstNode<'c, Op>
where
    Op: OpTrait<'c>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AstNode").field("op", &self.op).finish()
    }
}

impl<'c, Op> Hash for AstNode<'c, Op>
where
    Op: OpTrait<'c>,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}

impl<'c, Op> PartialEq for AstNode<'c, Op>
where
    Op: OpTrait<'c>,
{
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash
    }
}

impl<'c, Op> HasContext<'c> for AstNode<'c, Op>
where
    Op: OpTrait<'c>,
{
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c, Op> AstNodeTrait<'c, Op> for AstNode<'c, Op>
where
    Op: OpTrait<'c> + 'c,
{
    fn symbolic(&self) -> bool {
        self.symbolic
    }

    fn variables(&self) -> &HashSet<String> {
        &self.variables
    }

    fn child_iter(&self) -> Box<dyn Iterator<Item = AstRef<'c, Op>> + 'c> {
        self.op.child_iter()
    }
}

impl<'c, Op> AstNode<'c, Op>
where
    Op: OpTrait<'c> + 'c,
{
    pub(crate) fn new(ctx: &'c Context<'c>, op: Op, hash: u64) -> Self {
        let symbolic = op.child_iter().any(|child| child.symbolic());
        let variables = op
            .child_iter()
            .flat_map(|child| child.variables().clone().into_iter())
            .collect::<HashSet<String>>();

        Self {
            op,
            ctx,
            hash,
            symbolic,
            variables,
        }
    }

    pub fn op(&self) -> &Op {
        &self.op
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

    pub fn child_iter(&self) -> Box<dyn Iterator<Item = AstRef<'c, Op>> + 'c> {
        self.op.child_iter()
    }

    pub fn children(&self) -> Vec<AstRef<'c, Op>> {
        self.op.children()
    }

    pub fn is_true(&self) -> bool {
        self.op.is_true()
    }

    pub fn is_false(&self) -> bool {
        self.op.is_false()
    }
}

pub type AstRef<'c, Op> = Arc<AstNode<'c, Op>>;
