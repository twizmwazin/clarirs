use ahash::AHasher;
use std::{
    collections::HashSet,
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
    fn make_bool_annotated(
        &'c self,
        op: BooleanOp<'c>,
        mut annotations: HashSet<Annotation>,
    ) -> Result<BoolAst<'c>, ClarirsError> {
        annotations.extend(
            op.child_iter()
                .flat_map(|c| c.annotations())
                .filter(|a| a.relocatable()),
        );

        let mut hasher = AHasher::default();
        0u32.hash(&mut hasher); // Domain separation for bools
        op.hash(&mut hasher);
        for a in &annotations {
            a.hash(&mut hasher);
        }
        let hash = hasher.finish();

        Ok(self
            .ast_cache
            .get_or_insert(hash, || {
                Ok(DynAst::from(Arc::new(AstNode::new(
                    self,
                    op.clone(),
                    annotations.clone(),
                    hash,
                ))))
            })?
            .as_bool()
            .ok_or(ClarirsError::TypeError("Expected BoolAst".to_string()))?
            .clone())
    }

    fn make_bitvec_annotated(
        &'c self,
        op: BitVecOp<'c>,
        mut annotations: HashSet<Annotation>,
    ) -> Result<BitVecAst<'c>, ClarirsError> {
        annotations.extend(
            op.child_iter()
                .flat_map(|c| c.annotations())
                .filter(|a| a.relocatable()),
        );

        let mut hasher = AHasher::default();
        1u32.hash(&mut hasher); // Domain separation for bitvecs
        op.hash(&mut hasher);
        for a in &annotations {
            a.hash(&mut hasher);
        }
        let hash = hasher.finish();

        Ok(self
            .ast_cache
            .get_or_insert(hash, || {
                Ok(DynAst::from(Arc::new(AstNode::new(
                    self,
                    op.clone(),
                    annotations.clone(),
                    hash,
                ))))
            })?
            .as_bitvec()
            .ok_or(ClarirsError::TypeError("Expected BitVecAst".to_string()))?
            .clone())
    }

    fn make_float_annotated(
        &'c self,
        op: FloatOp<'c>,
        mut annotations: HashSet<Annotation>,
    ) -> std::result::Result<FloatAst<'c>, ClarirsError> {
        annotations.extend(
            op.child_iter()
                .flat_map(|c| c.annotations())
                .filter(|a| a.relocatable()),
        );

        let mut hasher = AHasher::default();
        2u32.hash(&mut hasher); // Domain separation for floats
        op.hash(&mut hasher);
        for a in &annotations {
            a.hash(&mut hasher);
        }
        let hash = hasher.finish();

        Ok(self
            .ast_cache
            .get_or_insert(hash, || {
                Ok(DynAst::from(Arc::new(AstNode::new(
                    self,
                    op.clone(),
                    annotations.clone(),
                    hash,
                ))))
            })?
            .as_float()
            .ok_or(ClarirsError::TypeError("Expected FloatAst".to_string()))?
            .clone())
    }

    fn make_string_annotated(
        &'c self,
        op: StringOp<'c>,
        mut annotations: HashSet<Annotation>,
    ) -> Result<StringAst<'c>, ClarirsError> {
        annotations.extend(
            op.child_iter()
                .flat_map(|c| c.annotations())
                .filter(|a| a.relocatable()),
        );

        let mut hasher = AHasher::default();
        3u32.hash(&mut hasher); // Domain separation for strings
        op.hash(&mut hasher);
        for a in &annotations {
            a.hash(&mut hasher);
        }
        let hash = hasher.finish();

        Ok(self
            .ast_cache
            .get_or_insert(hash, || {
                Ok(DynAst::from(Arc::new(AstNode::new(
                    self,
                    op.clone(),
                    annotations.clone(),
                    hash,
                ))))
            })?
            .as_string()
            .ok_or(ClarirsError::TypeError("Expected StringAst".to_string()))?
            .clone())
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
