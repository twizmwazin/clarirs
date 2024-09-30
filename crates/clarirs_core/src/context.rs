use ahash::AHasher;
use anyhow::Result;
use std::{
    collections::HashMap,
    fmt::Debug,
    hash::{Hash, Hasher},
    sync::{Arc, RwLock, Weak},
};

use crate::prelude::*;

#[derive(Debug, Default)]
pub struct Context<'c> {
    pub(crate) ast_cache: Arc<RwLock<HashMap<u64, Weak<AstNode<'c>>>>>,
    pub(crate) simplification_cache: Arc<RwLock<HashMap<u64, Weak<AstNode<'c>>>>>,
}

impl<'c> PartialEq for Context<'c> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.ast_cache, &other.ast_cache)
            && Arc::ptr_eq(&self.simplification_cache, &other.simplification_cache)
    }
}

impl<'c> Eq for Context<'c> {}

impl<'c> Context<'c> {
    pub fn new() -> Self {
        Self {
            ast_cache: Arc::new(RwLock::new(HashMap::new())),
            simplification_cache: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    // Cache optimization
    pub fn clear_cache(&self) -> Result<(), ClarirsError> {
        self.ast_cache.write().map(|mut c| c.clear())?;
        self.simplification_cache.write().map(|mut c| c.clear())?;
        Ok(())
    }
}

impl<'c> AstFactory<'c> for Context<'c> {
    fn make_ast(&'c self, op: AstOp<'c>) -> Result<AstRef<'c>, ClarirsError> {
        #[cfg(feature = "runtime-checks")]
        if !op.valid_args() {
            return Err(ClarirsError::InvalidArguments);
        }

        let mut hasher = AHasher::default();
        op.hash(&mut hasher);
        let hash = hasher.finish();

        Ok(self.ast_cache.write().map(|mut ast_cache| ast_cache
                .get(&hash)
                .and_then(|ast| ast.upgrade())
                .unwrap_or_else(|| {
                    let ast = Arc::new(AstNode::new(self, op, hash));
                    ast_cache.insert(hash, Arc::downgrade(&ast));
                    ast
                }))?)
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
