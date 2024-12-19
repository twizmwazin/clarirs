use ahash::AHasher;
use std::{
    fmt::Debug,
    hash::{Hash, Hasher},
    sync::Arc,
};

use crate::{ast::astcache::AstCache, prelude::*};

#[derive(Debug, Default)]
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

        let arc = self
            .ast_cache
            .get_or_insert_with_bv(hash, || Ok(Arc::new(AstNode::new(self, op, hash))))?;
        Ok(arc)
    }

    fn make_float(&'c self, op: FloatOp<'c>) -> std::result::Result<FloatAst<'c>, ClarirsError> {
        let mut hasher = AHasher::default();
        op.hash(&mut hasher);
        let hash = hasher.finish();

        let arc = self
            .ast_cache
            .get_or_insert_with_float(hash, || Ok(Arc::new(AstNode::new(self, op, hash))))?;
        Ok(arc)
    }

    fn make_string(&'c self, op: StringOp<'c>) -> std::result::Result<StringAst<'c>, ClarirsError> {
        let mut hasher = AHasher::default();
        op.hash(&mut hasher);
        let hash = hasher.finish();

        let arc = self
            .ast_cache
            .get_or_insert_with_string(hash, || Ok(Arc::new(AstNode::new(self, op, hash))))?;
        Ok(arc)
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
