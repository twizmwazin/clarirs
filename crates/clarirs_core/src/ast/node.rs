use std::{
    collections::BTreeSet,
    fmt::Debug,
    hash::{Hash, Hasher},
    sync::Arc,
};

use serde::Serialize;

use crate::{
    ast::{
        bitvec::BitVecOpChildIter, bool::BooleanOpChildIter, factory_support::SupportsAnnotate,
        float::FloatOpChildIter, string::StringOpChildIter,
    },
    prelude::*,
};

#[derive(Clone, Eq, serde::Serialize)]
pub struct AstNode<'c, O: Op<'c>> {
    op: O,
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
}

impl<'c, O> Drop for AstNode<'c, O>
where
    O: Op<'c>,
{
    fn drop(&mut self) {
        self.ctx.drop_cache(self.hash);
    }
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
        self.op == other.op && self.annotations == other.annotations
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

impl<'c, O: Op<'c> + Serialize + SupportsAnnotate<'c>> AstNode<'c, O> {
    pub(crate) fn new(
        ctx: &'c Context<'c>,
        op: O,
        annotations: BTreeSet<Annotation>,
        hash: u64,
        size: u32,
    ) -> Self {
        let variables = op.variables();
        let depth = op.depth();
        // Symbolic propagates from: having variables, the op itself being symbolic
        // (e.g. VSA Union/Intersection/Widen), or any child being symbolic
        let symbolic =
            !variables.is_empty() || op.symbolic() || op.child_iter().any(|c| c.symbolic());

        Self {
            op,
            ctx,
            hash,
            variables,
            depth,
            size,
            annotations,
            symbolic,
        }
    }

    pub fn op(&self) -> &O {
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
}

impl<'c, O: Op<'c>> Op<'c> for AstNode<'c, O> {
    type ChildIter<'a>
        = O::ChildIter<'a>
    where
        Self: 'a;

    fn child_iter(&self) -> Self::ChildIter<'_> {
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

    fn symbolic(&self) -> bool {
        self.symbolic
    }

    fn variables(&self) -> BTreeSet<InternedString> {
        self.variables.clone()
    }

    fn check_same_sort(&self, other: &Self) -> bool {
        self.op.check_same_sort(&other.op)
    }
}

pub type AstRef<'c, Op> = Arc<AstNode<'c, Op>>;

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

#[derive(Clone, Eq, PartialEq, Hash, Debug, Serialize)]
pub enum DynAst<'c> {
    Boolean(BoolAst<'c>),
    BitVec(BitVecAst<'c>),
    Float(FloatAst<'c>),
    String(StringAst<'c>),
}

pub enum DynAstChildIter<'a, 'c> {
    Boolean(BooleanOpChildIter<'a, 'c>),
    BitVec(BitVecOpChildIter<'a, 'c>),
    Float(FloatOpChildIter<'a, 'c>),
    String(StringOpChildIter<'a, 'c>),
}

/// Dispatches a method call across all DynAst variants. This must be a macro
/// rather than a function because each variant has a different concrete type
/// (BoolAst, BitVecAst, etc.), and Rust closures cannot be generic over them.
macro_rules! dynast_dispatch {
    ($self:expr, |$ast:ident| $body:expr) => {
        match $self {
            DynAst::Boolean($ast) => $body,
            DynAst::BitVec($ast) => $body,
            DynAst::Float($ast) => $body,
            DynAst::String($ast) => $body,
        }
    };
}

/// Dispatches a method call across all DynAstChildIter variants. Same reasoning
/// as `dynast_dispatch!` for why this is a macro.
macro_rules! dynast_iter_dispatch {
    ($self:expr, |$iter:ident| $body:expr) => {
        match $self {
            DynAstChildIter::Boolean($iter) => $body,
            DynAstChildIter::BitVec($iter) => $body,
            DynAstChildIter::Float($iter) => $body,
            DynAstChildIter::String($iter) => $body,
        }
    };
}

impl<'a, 'c> Iterator for DynAstChildIter<'a, 'c> {
    type Item = DynAst<'c>;

    fn next(&mut self) -> Option<Self::Item> {
        dynast_iter_dispatch!(self, |iter| iter.next())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        dynast_iter_dispatch!(self, |iter| iter.size_hint())
    }
}

impl<'a, 'c> ExactSizeIterator for DynAstChildIter<'a, 'c> {
    fn len(&self) -> usize {
        dynast_iter_dispatch!(self, |iter| iter.len())
    }
}

impl DynAst<'_> {
    pub fn annotations(&self) -> BTreeSet<Annotation> {
        dynast_dispatch!(self, |ast| ast.annotations().clone())
    }

    pub fn symbolic(&self) -> bool {
        dynast_dispatch!(self, |ast| ast.symbolic())
    }
}

impl<'c> HasContext<'c> for DynAst<'c> {
    fn context(&self) -> &'c Context<'c> {
        dynast_dispatch!(self, |ast| ast.context())
    }
}

impl<'c> Op<'c> for DynAst<'c> {
    type ChildIter<'a>
        = DynAstChildIter<'a, 'c>
    where
        Self: 'a;

    fn child_iter(&self) -> Self::ChildIter<'_> {
        match self {
            DynAst::Boolean(ast) => DynAstChildIter::Boolean(ast.op().child_iter()),
            DynAst::BitVec(ast) => DynAstChildIter::BitVec(ast.op().child_iter()),
            DynAst::Float(ast) => DynAstChildIter::Float(ast.op().child_iter()),
            DynAst::String(ast) => DynAstChildIter::String(ast.op().child_iter()),
        }
    }

    fn depth(&self) -> u32 {
        dynast_dispatch!(self, |ast| ast.depth())
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

    fn variables(&self) -> BTreeSet<InternedString> {
        dynast_dispatch!(self, |ast| ast.variables()).clone()
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
        dynast_dispatch!(self, |ast| ast.hash)
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

/// Generates From<AstType> and From<&AstType> for DynAst, plus TryFrom<DynAst> for AstType.
macro_rules! impl_dynast_conversions {
    ($( $Variant:ident($AstType:ty, $err:expr) ),* $(,)?) => {
        $(
            impl<'c> From<$AstType> for DynAst<'c> {
                fn from(ast: $AstType) -> Self {
                    DynAst::$Variant(ast.clone())
                }
            }

            impl<'c> From<&$AstType> for DynAst<'c> {
                fn from(ast: &$AstType) -> Self {
                    DynAst::$Variant(ast.clone())
                }
            }

            impl<'c> TryFrom<DynAst<'c>> for $AstType {
                type Error = ClarirsError;

                fn try_from(value: DynAst<'c>) -> Result<Self, Self::Error> {
                    match value {
                        DynAst::$Variant(ast) => Ok(ast),
                        _ => Err(ClarirsError::TypeError($err.to_string())),
                    }
                }
            }
        )*
    };
}

impl_dynast_conversions!(
    Boolean(BoolAst<'c>, "Expected BoolAst"),
    BitVec(BitVecAst<'c>, "Expected BitVecAst"),
    Float(FloatAst<'c>, "Expected FloatAst"),
    String(StringAst<'c>, "Expected StringAst"),
);
