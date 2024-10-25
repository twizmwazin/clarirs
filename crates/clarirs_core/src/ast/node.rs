use std::{
    collections::HashSet,
    fmt::Debug,
    hash::{Hash, Hasher},
    sync::Arc,
};

use serde::{Serialize, Serializer};

use crate::context::{Context, HasContext};

use super::kind::AstKind; // op::AstOp

// pub trait OpTrait<'c>: Debug + Serialize {
//     // type ChildOps: 'c;

//     fn child_iter(&self) -> Box<dyn Iterator<Item = AstRef<'c, Self::ChildOps>> + 'c>;

//     fn children(&self) -> Vec<AstRef<'c, Self>> {
//         self.child_iter().collect()
//     }

//     fn is_true(&self) -> bool {
//         false
//     }

//     fn is_false(&self) -> bool {
//         false
//     }
// }

pub trait OpTrait<'c>: Debug + Serialize {
    // type Child: OpTrait<'c> + Serialize;
    type Child;

    fn child_iter(&self) -> Box<dyn Iterator<Item = AstRef<'c, Self::Child>> + 'c>;

    // fn children(&self) -> Vec<AstRef<'c, Self>> {
    //     self.child_iter().collect()
    // }

    // Optional methods
    fn is_true(&self) -> bool {
        false
    }

    fn is_false(&self) -> bool {
        false
    }
}

// pub struct SerializableOpTrait<'c>(pub Box<dyn OpTrait<'c> + 'c>);

// impl<'c> Serialize for SerializableOpTrait<'c> {
//     fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
//     where
//         S: Serializer,
//     {
//         // Implement serialization logic here
//         // For example, you can serialize the inner trait object as a string
//         let type_name = std::any::type_name::<Box<dyn OpTrait<'c>>>();
//         serializer.serialize_str(type_name)
//     }
// }

pub trait AstNodeTrait<'c, Op>: Debug + Serialize
where
    Op: OpTrait<'c> + Serialize,
{
    fn symbolic(&self) -> bool;
    fn variables(&self) -> &HashSet<String>;
    fn child_iter(&self) -> Box<dyn Iterator<Item = AstRef<'c, Op>> + 'c>;
}

#[derive(Clone, Eq, Serialize)]
pub struct AstNode<'c, Op>
where
    Op: OpTrait<'c> + Serialize,
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
    Op: OpTrait<'c> + Serialize,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AstNode").field("op", &self.op).finish()
    }
}

impl<'c, Op> Hash for AstNode<'c, Op>
where
    Op: OpTrait<'c> + Serialize,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}

impl<'c, Op> PartialEq for AstNode<'c, Op>
where
    Op: OpTrait<'c> + Serialize,
{
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash
    }
}

impl<'c, Op> HasContext<'c> for AstNode<'c, Op>
where
    Op: OpTrait<'c> + Serialize,
{
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c, Op> AstNodeTrait<'c, Op> for AstNode<'c, Op>
where
    Op: OpTrait<'c> + Serialize + 'c,
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
    Op: OpTrait<'c> + Serialize ,
{
    pub(crate) fn new(ctx: &'c Context<'c>, op: Op, hash: u64) -> Self {
        let symbolic = op.child_iter().any(|child| child.symbolic());
        let variables = op
            .child_iter()
            .flat_map(|child| child.variables().clone().into_iter())
            .collect::<HashSet<String>>();

        Self {
            op: Box::new(op), // Use Box to handle the size issue
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
