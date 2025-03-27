use ahash::AHasher;
use std::{
    fmt::Debug,
    hash::{Hash, Hasher},
    sync::Arc,
};

use crate::{ast::astcache::AstCache, prelude::*};

#[derive(Debug, Default)]
#[allow(dead_code)] // FIXME: reintroduce simplification cache
pub struct Context<'c> {
    pub(crate) ast_cache: AstCache<'c>,
    pub(crate) simplification_cache: AstCache<'c>,
}

impl PartialEq for Context<'_> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}

impl Eq for Context<'_> {}

unsafe impl Send for Context<'_> {}
unsafe impl Sync for Context<'_> {}

impl Context<'_> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<'c> AstFactory<'c> for Context<'c> {
    fn make_bool(&'c self, op: BooleanOp<'c>) -> std::result::Result<BoolAst<'c>, ClarirsError> {
        let mut hasher = AHasher::default();
        op.hash(&mut hasher);
        let hash = hasher.finish();

        let arc = self
            .ast_cache
            .get_or_insert_with_bool(hash, || Ok(Arc::new(AstNode::new(self, op, hash))))?;
        Ok(arc)
    }

    fn make_bitvec(&'c self, op: BitVecOp<'c>) -> std::result::Result<BitVecAst<'c>, ClarirsError> {
        let mut hasher = AHasher::default();
        op.hash(&mut hasher);
        let hash = hasher.finish();

        let mut result = self
            .ast_cache
            .get_or_insert_with_bv(hash, || Ok(Arc::new(AstNode::new(self, op.clone(), hash))))?;

        // If the op is not Annotation, copy all relocatable annotations from the children
        if !matches!(op, BitVecOp::Annotated(..)) {
            result = result
                .children()
                .iter()
                .flat_map(|child| child.get_annotations())
                .filter(|annotation| annotation.relocatable())
                .collect::<Vec<Annotation>>()
                .iter()
                .try_fold(result, |result, annotation| {
                    self.make_bitvec(BitVecOp::Annotated(result.clone(), annotation.clone()))
                })?;
        }

        Ok(result)
    }

    fn make_float(&'c self, op: FloatOp<'c>) -> std::result::Result<FloatAst<'c>, ClarirsError> {
        let mut hasher = AHasher::default();
        op.hash(&mut hasher);
        let hash = hasher.finish();

        let mut result = self.ast_cache.get_or_insert_with_float(hash, || {
            Ok(Arc::new(AstNode::new(self, op.clone(), hash)))
        })?;

        // If the op is not Annotation, copy all relocatable annotations from the children
        if !matches!(op, FloatOp::Annotated(..)) {
            result = result
                .children()
                .iter()
                .flat_map(|child| child.get_annotations())
                .filter(|annotation| annotation.relocatable())
                .collect::<Vec<Annotation>>()
                .iter()
                .try_fold(result, |result, annotation| {
                    self.make_float(FloatOp::Annotated(result.clone(), annotation.clone()))
                })?;
        }

        Ok(result)
    }

    fn make_string(&'c self, op: StringOp<'c>) -> std::result::Result<StringAst<'c>, ClarirsError> {
        let mut hasher = AHasher::default();
        op.hash(&mut hasher);
        let hash = hasher.finish();

        let mut result = self.ast_cache.get_or_insert_with_string(hash, || {
            Ok(Arc::new(AstNode::new(self, op.clone(), hash)))
        })?;

        // If the op is not Annotation, copy all relocatable annotations from the children
        if !matches!(op, StringOp::Annotated(..)) {
            result = result
                .children()
                .iter()
                .flat_map(|child| child.get_annotations())
                .filter(|annotation| annotation.relocatable())
                .collect::<Vec<Annotation>>()
                .iter()
                .try_fold(result, |result, annotation| {
                    self.make_string(StringOp::Annotated(result.clone(), annotation.clone()))
                })?;
        }

        Ok(result)
    }
}

pub trait HasContext<'c> {
    fn context(&self) -> &'c Context<'c>;
}

impl<'c, T> HasContext<'c> for Arc<T>
where
    T: HasContext<'c>,
{
    fn context(&self) -> &'c Context<'c> {
        self.as_ref().context()
    }
}
