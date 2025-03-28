use std::{
    collections::HashMap,
    hash::Hash,
    sync::{Arc, RwLock, Weak},
};

use crate::prelude::*;

/// A trait for caching values based on a key. In the context of clarirs, this
/// is used to cache ASTs, as well as the results of various algorithms.
/// The `get_or_insert` method will either return the cached value or compute
/// a new value and insert it into the cache.
pub trait Cache<K, V, E: Into<ClarirsError> = ClarirsError> {
    fn get_or_insert(&self, key: K, value_cv: impl FnMut() -> Result<V, E>) -> Result<V, E>;
}

impl<K, V, E: Into<ClarirsError>> Cache<K, V, E> for () {
    fn get_or_insert(&self, _: K, mut value_cv: impl FnMut() -> Result<V, E>) -> Result<V, E> {
        value_cv()
    }
}

/// A generic cache implementation that uses a `HashMap` to store key-value pairs.
#[derive(Debug, Default)]
pub struct GenericCache<K, V>(RwLock<HashMap<K, V>>);

impl<K: Hash + Eq, V: Clone> Cache<K, V> for GenericCache<K, V> {
    fn get_or_insert(
        &self,
        key: K,
        mut value_cv: impl FnMut() -> Result<V, ClarirsError>,
    ) -> Result<V, ClarirsError> {
        let mut locked = self.0.write().unwrap();
        match locked.get(&key) {
            Some(value) => Ok(value.clone()),
            None => {
                let value = value_cv()?;
                locked.insert(key, value.clone());
                Ok(value)
            }
        }
    }
}

#[derive(Debug)]
enum AstCacheValue<'c> {
    Boolean(Weak<AstNode<'c, BooleanOp<'c>>>),
    BitVec(Weak<AstNode<'c, BitVecOp<'c>>>),
    Float(Weak<AstNode<'c, FloatOp<'c>>>),
    String(Weak<AstNode<'c, StringOp<'c>>>),
}

/// A special cache for when the result type is an AST. Unlike the generic cache,
/// this cache stores weak references to the AST nodes.
#[derive(Debug, Default)]
pub struct AstCache<'c>(RwLock<HashMap<u64, AstCacheValue<'c>>>);

impl<'c> Cache<u64, DynAst<'c>> for AstCache<'c> {
    fn get_or_insert(
        &self,
        hash: u64,
        f: impl FnOnce() -> Result<DynAst<'c>, ClarirsError>,
    ) -> Result<DynAst<'c>, ClarirsError> {
        // Step 1: Try to get a read lock and check if the value is already in the cache
        {
            let inner = self.0.read().unwrap();
            if let Some(value) = inner.get(&hash) {
                if let Some(arc) = match value {
                    AstCacheValue::Boolean(weak) => weak.upgrade().map(DynAst::Boolean),
                    AstCacheValue::BitVec(weak) => weak.upgrade().map(DynAst::BitVec),
                    AstCacheValue::Float(weak) => weak.upgrade().map(DynAst::Float),
                    AstCacheValue::String(weak) => weak.upgrade().map(DynAst::String),
                } {
                    return Ok(arc);
                }
            }
            // Value not found or expired; we'll compute it next
        } // Read lock is dropped here

        // Step 2: Compute the value without holding any lock
        let arc = f()?; // This may call `simplify()` and recurse

        // Step 3: Acquire a write lock to insert the new value
        let mut inner = self.0.write().unwrap();

        match &arc {
            DynAst::Boolean(ast) => {
                inner.insert(hash, AstCacheValue::Boolean(Arc::downgrade(ast)));
            }
            DynAst::BitVec(ast) => {
                inner.insert(hash, AstCacheValue::BitVec(Arc::downgrade(ast)));
            }
            DynAst::Float(ast) => {
                inner.insert(hash, AstCacheValue::Float(Arc::downgrade(ast)));
            }
            DynAst::String(ast) => {
                inner.insert(hash, AstCacheValue::String(Arc::downgrade(ast)));
            }
        }

        Ok(arc)
    }
}
