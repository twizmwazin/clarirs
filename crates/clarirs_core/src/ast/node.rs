use std::{
    collections::HashSet,
    fmt::Debug,
    hash::{Hash, Hasher},
    sync::Arc,
};

use serde::Serialize;

use crate::ast::op::BooleanOp;
use crate::context::{Context, HasContext};

use super::kind::AstKind; // op::AstOp

// Trait that all operation types must implement.
pub trait OpTrait<'c>: Debug + Serialize {
    fn child_iter(&self) -> Box<dyn Iterator<Item = &AstRef<'c>> + 'c> ;

    fn children(&self) -> Vec<AstRef<'c>> ;

    fn is_true(&self) -> bool {
        false
    }

    fn is_false(&self) -> bool {
        false
    }
}

// impl<'c> OpTrait<'c> for BooleanOp<'c> {
//     fn child_iter(&self) -> Box<dyn Iterator<Item = &AstRef<'c>> + 'c> ;

//     fn children(&self) ->  Vec<AstRef<'c>> ;

//     // Override is_true and is_false
//     fn is_true(&self) -> bool {
//         matches!(self, BooleanOp::BoolV(true))
//     }

//     fn is_false(&self) -> bool {
//         matches!(self, BooleanOp::BoolV(false))
//     }
// }

pub trait AstNodeTrait<'c>: Debug + Serialize {
    fn symbolic(&self) -> bool;
    fn variables(&self) -> &HashSet<String>;
    fn child_iter(&self) -> Box<dyn Iterator<Item = &AstRef<'c>> + 'c>;
    fn as_any(&self) -> &dyn std::any::Any;
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

// Implement AstNodeTrait for AstNode
impl<'c, Op> AstNodeTrait<'c> for AstNode<'c, Op>
where
    Op: OpTrait<'c> + 'c,
{
    fn symbolic(&self) -> bool {
        self.symbolic
    }

    fn variables(&self) -> &HashSet<String> {
        &self.variables
    }

    fn child_iter(&self) -> Box<dyn Iterator<Item = &AstRef<'c>> + 'c> {
        self.op.child_iter()
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
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
            .flat_map(|child| child.variables().iter().cloned())
            .collect();

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

    pub fn child_iter(&self) -> Box<dyn Iterator<Item = &AstRef<'c>> + 'c> {
        self.op.child_iter()
    }

    pub fn children(&self) -> Vec<AstRef<'c>> {
        self.op.children()
    }

    pub fn is_true(&self) -> bool {
        self.op.is_true()
    }

    pub fn is_false(&self) -> bool {
        self.op.is_false()
    }
}

// pub type AstRef<'c> = Arc<dyn AstNodeTrait<'c> + 'c>;

pub type AstRef<'c> = Arc<AstNode<'c>>; // Won't work as AstNode is now generic


// #[derive(Clone, Eq, Serialize)]
// pub struct AstNode<'c> {
//     // Everything can be derived from the op
//     op: AstOp<'c>,

//     #[serde(skip)]
//     ctx: &'c Context<'c>,
//     #[serde(skip)]
//     kind: AstKind,
//     #[serde(skip)]
//     hash: u64,
//     #[serde(skip)]
//     symbolic: bool,
//     #[serde(skip)]
//     variables: HashSet<String>,
// }

// impl Debug for AstNode<'_> {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         f.debug_struct("AstNode").field("op", &self.op).finish()
//     }
// }

// impl Hash for AstNode<'_> {
//     fn hash<H: Hasher>(&self, state: &mut H) {
//         state.write_u64(self.hash);
//     }
// }

// impl PartialEq for AstNode<'_> {
//     fn eq(&self, other: &Self) -> bool {
//         self.hash == other.hash
//     }
// }

// impl<'c> HasContext<'c> for AstNode<'c> {
//     fn context(&self) -> &'c Context<'c> {
//         self.ctx
//     }
// }

// impl<'c> AstNode<'c> {
//     pub(crate) fn new(ctx: &'c Context<'c>, op: AstOp<'c>, hash: u64) -> Self {
//         let kind = op.kind();
//         let symbolic = op.child_iter().any(|child| child.symbolic());
//         let variables = op
//             .child_iter()
//             .flat_map(|child| child.variables().iter().cloned())
//             .collect();

//         Self {
//             op,
//             ctx,
//             kind,
//             hash,
//             symbolic,
//             variables,
//         }
//     }

//     pub fn op(&self) -> &AstOp<'c> {
//         &self.op
//     }

//     pub fn kind(&self) -> AstKind {
//         self.kind.clone()
//     }

//     pub fn hash(&self) -> u64 {
//         self.hash
//     }

//     pub fn symbolic(&self) -> bool {
//         self.symbolic
//     }

//     pub fn variables(&self) -> &HashSet<String> {
//         &self.variables
//     }

//     pub fn child_iter(&self) -> impl Iterator<Item = &AstRef<'c>> {
//         self.op.child_iter()
//     }

//     pub fn children(&self) -> Vec<&AstRef<'c>> {
//         self.op.children()
//     }

//     pub fn is_true(&self) -> bool {
//         matches!(self.op, AstOp::BooleanOp(BooleanOp::BoolV(true)))
//     }

//     pub fn is_false(&self) -> bool {
//         matches!(self.op, AstOp::BooleanOp(BooleanOp::BoolV(false)))
//     }
// }
