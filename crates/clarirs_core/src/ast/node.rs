use std::{
    collections::HashSet,
    fmt::Debug,
    hash::{Hash, Hasher},
    sync::Arc,
    vec::IntoIter,
};

use serde::Serialize;

use crate::prelude::*;

#[derive(Clone, Eq, serde::Serialize)]
pub struct AstNode<'c, O: Op<'c>> {
    op: O,
    #[serde(skip)]
    ctx: &'c Context<'c>,
    #[serde(skip)]
    hash: u64,
    #[serde(skip)]
    symbolic: bool,
    #[serde(skip)]
    variables: HashSet<String>,
    #[serde(skip)]
    depth: u32,
}

impl<'c, O> Debug for AstNode<'c, O>
where
    O: Op<'c>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AstNode").field("op", &self.op).finish()
    }
}

impl<'c, O> Hash for AstNode<'c, O>
where
    O: Op<'c> + Serialize,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}

impl<'c, O> PartialEq for AstNode<'c, O>
where
    O: Op<'c> + Serialize,
{
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash
    }
}

impl<'c, O> HasContext<'c> for AstNode<'c, O>
where
    O: Op<'c> + Serialize,
{
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c, O: Op<'c> + Serialize> AstNode<'c, O> {
    pub(crate) fn new(ctx: &'c Context<'c>, op: O, hash: u64) -> Self {
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
            depth: 0, // TODO: Implement depth calculation
        }
    }

    pub fn op(&self) -> &O {
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

    pub fn depth(&self) -> u32 {
        self.depth
    }
}

impl<'c, O: Op<'c>> Op<'c> for AstNode<'c, O> {
    fn child_iter(&self) -> IntoIter<VarAst<'c>> {
        self.op.child_iter()
    }

    fn is_true(&self) -> bool {
        self.op.is_true()
    }

    fn is_false(&self) -> bool {
        self.op.is_false()
    }

    fn variables(&self) -> HashSet<String> {
        self.variables.clone()
    }
}

pub type AstRef<'c, Op> = Arc<AstNode<'c, Op>>;

#[derive(Clone, Eq, PartialEq, Hash, Debug, Serialize)]
pub enum VarAst<'c> {
    Boolean(BoolAst<'c>),
    BitVec(BitVecAst<'c>),
    Float(FloatAst<'c>),
    String(StringAst<'c>),
}

impl<'c> Op<'c> for VarAst<'c> {
    fn child_iter(&self) -> IntoIter<VarAst<'c>> {
        match self {
            VarAst::Boolean(ast) => ast.child_iter(),
            VarAst::BitVec(ast) => ast.child_iter(),
            VarAst::Float(ast) => ast.child_iter(),
            VarAst::String(ast) => ast.child_iter(),
        }
    }

    fn is_true(&self) -> bool {
        match self {
            VarAst::Boolean(ast) => ast.is_true(),
            _ => false,
        }
    }

    fn is_false(&self) -> bool {
        match self {
            VarAst::Boolean(ast) => ast.is_false(),
            _ => false,
        }
    }

    fn variables(&self) -> HashSet<String> {
        match self {
            VarAst::Boolean(ast) => ast.variables(),
            VarAst::BitVec(ast) => ast.variables(),
            VarAst::Float(ast) => ast.variables(),
            VarAst::String(ast) => ast.variables(),
        }
        .clone()
    }
}

impl<'c> From<&BoolAst<'c>> for VarAst<'c> {
    fn from(ast: &BoolAst<'c>) -> Self {
        VarAst::Boolean(ast.clone())
    }
}

impl<'c> From<&BitVecAst<'c>> for VarAst<'c> {
    fn from(ast: &BitVecAst<'c>) -> Self {
        VarAst::BitVec(ast.clone())
    }
}

impl<'c> From<&FloatAst<'c>> for VarAst<'c> {
    fn from(ast: &FloatAst<'c>) -> Self {
        VarAst::Float(ast.clone())
    }
}

impl<'c> From<&StringAst<'c>> for VarAst<'c> {
    fn from(ast: &StringAst<'c>) -> Self {
        VarAst::String(ast.clone())
    }
}
