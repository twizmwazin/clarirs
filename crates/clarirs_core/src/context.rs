use ahash::AHasher;
use std::{
    fmt::Debug,
    hash::{Hash, Hasher},
    sync::Arc,
};

use crate::{
    cache::{AstCache, Cache},
    prelude::*,
};

#[derive(Debug, Default)]
#[allow(dead_code)] // FIXME: reintroduce simplification cache
pub struct Context<'c> {
    pub(crate) ast_cache: AstCache<'c>,
    pub(crate) simplification_cache: AstCache<'c>,
    pub(crate) excavate_ite_cache: AstCache<'c>,
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

        let mut result = self
            .ast_cache
            .get_or_insert(hash, || {
                Ok(DynAst::from(Arc::new(AstNode::new(self, op.clone(), hash))))
            })?
            .as_bool()
            .ok_or(ClarirsError::TypeError("Expected BoolAst".to_string()))?
            .clone();

        // If the op is not Annotation, copy all relocatable annotations from the children
        if !matches!(op, BooleanOp::Annotated(..)) {
            result = result
                .children()
                .iter()
                .flat_map(|child| child.get_annotations())
                .filter(|annotation| annotation.relocatable())
                .collect::<Vec<Annotation>>()
                .iter()
                .try_fold(result, |result, annotation| {
                    self.make_bool(BooleanOp::Annotated(result.clone(), annotation.clone()))
                })?;
        }

        Ok(result)
    }

    fn make_bitvec(&'c self, op: BitVecOp<'c>) -> std::result::Result<BitVecAst<'c>, ClarirsError> {
        let mut hasher = AHasher::default();
        op.hash(&mut hasher);
        let hash = hasher.finish();

        let mut result = self
            .ast_cache
            .get_or_insert(hash, || {
                Ok(DynAst::from(Arc::new(AstNode::new(self, op.clone(), hash))))
            })?
            .as_bitvec()
            .ok_or(ClarirsError::TypeError("Expected BitVecAst".to_string()))?
            .clone();

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

        let mut result = self
            .ast_cache
            .get_or_insert(hash, || {
                Ok(DynAst::from(Arc::new(AstNode::new(self, op.clone(), hash))))
            })?
            .as_float()
            .ok_or(ClarirsError::TypeError("Expected FloatAst".to_string()))?
            .clone();

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

        let mut result = self
            .ast_cache
            .get_or_insert(hash, || {
                Ok(DynAst::from(Arc::new(AstNode::new(self, op.clone(), hash))))
            })?
            .as_string()
            .ok_or(ClarirsError::TypeError("Expected StringAst".to_string()))?
            .clone();

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
