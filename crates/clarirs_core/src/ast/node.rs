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
    variables: HashSet<String>,
    #[serde(skip)]
    depth: u32,
    #[serde(skip)]
    annotations: Vec<Annotation>,
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
        let variables = op.variables();
        let depth = op.depth();
        let annotations = op.get_annotations();

        Self {
            op,
            ctx,
            hash,
            variables,
            depth,
            annotations,
        }
    }

    pub fn op(&self) -> &O {
        &self.op
    }

    pub fn hash(&self) -> u64 {
        self.hash
    }

    pub fn symbolic(&self) -> bool {
        !self.variables.is_empty()
    }

    pub fn variables(&self) -> &HashSet<String> {
        &self.variables
    }
}

impl<'c, O: Op<'c>> Op<'c> for AstNode<'c, O> {
    fn child_iter(&self) -> IntoIter<DynAst<'c>> {
        self.op.child_iter()
    }

    fn depth(&self) -> u32 {
        self.depth
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

    fn get_annotations(&self) -> Vec<Annotation> {
        self.annotations.clone()
    }

    fn check_same_sort(&self, other: &Self) -> bool {
        self.op().check_same_sort(other.op())
    }
}

pub type AstRef<'c, Op> = Arc<AstNode<'c, Op>>;

#[derive(Clone, Eq, PartialEq, Hash, Debug, Serialize)]
pub enum DynAst<'c> {
    Boolean(BoolAst<'c>),
    BitVec(BitVecAst<'c>),
    Float(FloatAst<'c>),
    String(StringAst<'c>),
}

impl<'c> HasContext<'c> for DynAst<'c> {
    fn context(&self) -> &'c Context<'c> {
        match self {
            DynAst::Boolean(ast) => ast.context(),
            DynAst::BitVec(ast) => ast.context(),
            DynAst::Float(ast) => ast.context(),
            DynAst::String(ast) => ast.context(),
        }
    }
}

impl<'c> Op<'c> for DynAst<'c> {
    fn child_iter(&self) -> IntoIter<DynAst<'c>> {
        match self {
            DynAst::Boolean(ast) => ast.child_iter(),
            DynAst::BitVec(ast) => ast.child_iter(),
            DynAst::Float(ast) => ast.child_iter(),
            DynAst::String(ast) => ast.child_iter(),
        }
    }

    fn depth(&self) -> u32 {
        match self {
            DynAst::Boolean(ast) => ast.depth(),
            DynAst::BitVec(ast) => ast.depth(),
            DynAst::Float(ast) => ast.depth(),
            DynAst::String(ast) => ast.depth(),
        }
    }

    fn is_true(&self) -> bool {
        match self {
            DynAst::Boolean(ast) => ast.is_true(),
            _ => false,
        }
    }

    fn is_false(&self) -> bool {
        match self {
            DynAst::Boolean(ast) => ast.is_false(),
            _ => false,
        }
    }

    fn variables(&self) -> HashSet<String> {
        match self {
            DynAst::Boolean(ast) => ast.variables(),
            DynAst::BitVec(ast) => ast.variables(),
            DynAst::Float(ast) => ast.variables(),
            DynAst::String(ast) => ast.variables(),
        }
        .clone()
    }

    fn get_annotations(&self) -> Vec<Annotation> {
        match self {
            DynAst::Boolean(ast) => ast.get_annotations(),
            DynAst::BitVec(ast) => ast.get_annotations(),
            DynAst::Float(ast) => ast.get_annotations(),
            DynAst::String(ast) => ast.get_annotations(),
        }
    }

    fn check_same_sort(&self, other: &Self) -> bool {
        match (self, other) {
            (DynAst::Boolean(a), DynAst::Boolean(b)) => a.check_same_sort(b),
            (DynAst::BitVec(a), DynAst::BitVec(b)) => a.check_same_sort(b),
            (DynAst::Float(a), DynAst::Float(b)) => a.check_same_sort(b),
            (DynAst::String(a), DynAst::String(b)) => a.check_same_sort(b),
            _ => false,
        }
    }
}

impl<'c> DynAst<'c> {
    pub fn inner_hash(&self) -> u64 {
        match self {
            DynAst::Boolean(ast) => ast.hash,
            DynAst::BitVec(ast) => ast.hash,
            DynAst::Float(ast) => ast.hash,
            DynAst::String(ast) => ast.hash,
        }
    }

    pub fn as_bool(&self) -> Option<&BoolAst<'c>> {
        match self {
            DynAst::Boolean(ast) => Some(ast),
            _ => None,
        }
    }

    pub fn as_bitvec(&self) -> Option<&BitVecAst<'c>> {
        match self {
            DynAst::BitVec(ast) => Some(ast),
            _ => None,
        }
    }

    pub fn as_float(&self) -> Option<&FloatAst<'c>> {
        match self {
            DynAst::Float(ast) => Some(ast),
            _ => None,
        }
    }

    pub fn as_string(&self) -> Option<&StringAst<'c>> {
        match self {
            DynAst::String(ast) => Some(ast),
            _ => None,
        }
    }

    pub fn into_bool(self) -> Option<BoolAst<'c>> {
        match self {
            DynAst::Boolean(ast) => Some(ast),
            _ => None,
        }
    }

    pub fn into_bitvec(self) -> Option<BitVecAst<'c>> {
        match self {
            DynAst::BitVec(ast) => Some(ast),
            _ => None,
        }
    }

    pub fn into_float(self) -> Option<FloatAst<'c>> {
        match self {
            DynAst::Float(ast) => Some(ast),
            _ => None,
        }
    }

    pub fn into_string(self) -> Option<StringAst<'c>> {
        match self {
            DynAst::String(ast) => Some(ast),
            _ => None,
        }
    }
}

impl<'c> From<BoolAst<'c>> for DynAst<'c> {
    fn from(ast: BoolAst<'c>) -> Self {
        DynAst::Boolean(ast.clone())
    }
}

impl<'c> From<&BoolAst<'c>> for DynAst<'c> {
    fn from(ast: &BoolAst<'c>) -> Self {
        DynAst::Boolean(ast.clone())
    }
}

impl<'c> From<BitVecAst<'c>> for DynAst<'c> {
    fn from(ast: BitVecAst<'c>) -> Self {
        DynAst::BitVec(ast.clone())
    }
}

impl<'c> From<&BitVecAst<'c>> for DynAst<'c> {
    fn from(ast: &BitVecAst<'c>) -> Self {
        DynAst::BitVec(ast.clone())
    }
}

impl<'c> From<FloatAst<'c>> for DynAst<'c> {
    fn from(ast: FloatAst<'c>) -> Self {
        DynAst::Float(ast.clone())
    }
}

impl<'c> From<&FloatAst<'c>> for DynAst<'c> {
    fn from(ast: &FloatAst<'c>) -> Self {
        DynAst::Float(ast.clone())
    }
}

impl<'c> From<StringAst<'c>> for DynAst<'c> {
    fn from(ast: StringAst<'c>) -> Self {
        DynAst::String(ast.clone())
    }
}

impl<'c> From<&StringAst<'c>> for DynAst<'c> {
    fn from(ast: &StringAst<'c>) -> Self {
        DynAst::String(ast.clone())
    }
}

impl<'c> TryFrom<DynAst<'c>> for BoolAst<'c> {
    type Error = ClarirsError;

    fn try_from(value: DynAst<'c>) -> Result<Self, Self::Error> {
        match value {
            DynAst::Boolean(ast) => Ok(ast),
            _ => Err(ClarirsError::TypeError("Expected BoolAst".to_string())),
        }
    }
}

impl<'c> TryFrom<DynAst<'c>> for BitVecAst<'c> {
    type Error = ClarirsError;

    fn try_from(value: DynAst<'c>) -> Result<Self, Self::Error> {
        match value {
            DynAst::BitVec(ast) => Ok(ast),
            _ => Err(ClarirsError::TypeError("Expected BitVecAst".to_string())),
        }
    }
}

impl<'c> TryFrom<DynAst<'c>> for FloatAst<'c> {
    type Error = ClarirsError;

    fn try_from(value: DynAst<'c>) -> Result<Self, Self::Error> {
        match value {
            DynAst::Float(ast) => Ok(ast),
            _ => Err(ClarirsError::TypeError("Expected FloatAst".to_string())),
        }
    }
}

impl<'c> TryFrom<DynAst<'c>> for StringAst<'c> {
    type Error = ClarirsError;

    fn try_from(value: DynAst<'c>) -> Result<Self, Self::Error> {
        match value {
            DynAst::String(ast) => Ok(ast),
            _ => Err(ClarirsError::TypeError("Expected StringAst".to_string())),
        }
    }
}
