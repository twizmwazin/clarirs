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
        #[cfg(not(feature = "panic-on-hash-collision"))]
        {
            // Normal mode: Try to get from cache first, compute only if needed
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

        #[cfg(feature = "panic-on-hash-collision")]
        {
            // Collision detection mode: Always compute first, then check for collisions
            // Step 1: Compute the value without holding any lock
            let arc = f()?; // This may call `simplify()` and recurse

            // Step 2: Acquire a write lock to check for collisions and insert
            let mut inner = self.0.write().unwrap();

            // Check for hash collision
            if let Some(existing_value) = inner.get(&hash) {
                if let Some(existing_arc) = match existing_value {
                    AstCacheValue::Boolean(weak) => weak.upgrade().map(DynAst::Boolean),
                    AstCacheValue::BitVec(weak) => weak.upgrade().map(DynAst::BitVec),
                    AstCacheValue::Float(weak) => weak.upgrade().map(DynAst::Float),
                    AstCacheValue::String(weak) => weak.upgrade().map(DynAst::String),
                } {
                    if existing_arc != arc {
                        panic!(
                            "Hash collision detected! Hash: {hash}, Existing: {existing_arc:?}, New: {arc:?}"
                        );
                    }
                }
            }

            // Insert the new value
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(not(feature = "panic-on-hash-collision"))]
    fn test_ast_cache_basic() -> Result<(), ClarirsError> {
        let ctx = crate::context::Context::new();
        let cache = AstCache::default();

        // Create a simple AST
        let ast1 = ctx.bvv_prim_with_size(42u64, 64)?;
        let hash1 = 12345u64; // Arbitrary hash for testing

        // Insert into cache
        let result1 = cache.get_or_insert(hash1, || Ok(DynAst::from(&ast1)))?;

        // Verify we can retrieve it without recomputing
        let result2 =
            cache.get_or_insert(hash1, || panic!("Should not compute new value when cached"))?;

        assert_eq!(result1, result2);
        Ok(())
    }

    #[test]
    #[cfg(feature = "panic-on-hash-collision")]
    fn test_ast_cache_basic_collision_mode() -> Result<(), ClarirsError> {
        let ctx = crate::context::Context::new();
        let cache = AstCache::default();

        // Create a simple AST
        let ast1 = ctx.bvv_prim_with_size(42u64, 64)?;
        let hash1 = 12345u64; // Arbitrary hash for testing

        // Insert into cache
        let result1 = cache.get_or_insert(hash1, || Ok(DynAst::from(&ast1)))?;

        // In collision mode, it will always recompute, so provide a valid computation
        let ast2 = ctx.bvv_prim_with_size(42u64, 64)?;
        let result2 = cache.get_or_insert(hash1, || Ok(DynAst::from(&ast2)))?;

        assert_eq!(result1, result2);
        Ok(())
    }

    #[test]
    fn test_ast_cache_different_hashes() -> Result<(), ClarirsError> {
        let ctx = crate::context::Context::new();
        let cache = AstCache::default();

        let ast1 = ctx.bvv_prim_with_size(42u64, 64)?;
        let ast2 = ctx.bvv_prim_with_size(99u64, 64)?;

        let result1 = cache.get_or_insert(1, || Ok(DynAst::from(&ast1)))?;
        let result2 = cache.get_or_insert(2, || Ok(DynAst::from(&ast2)))?;

        // Different hashes should cache different values
        assert_ne!(result1, result2);
        Ok(())
    }

    #[test]
    #[cfg(not(feature = "panic-on-hash-collision"))]
    fn test_ast_cache_weak_reference_cleanup() -> Result<(), ClarirsError> {
        let ctx = crate::context::Context::new();
        let cache = AstCache::default();
        let hash = 999u64;

        {
            // Create and cache an AST
            let ast = ctx.bvv_prim_with_size(42u64, 64)?;
            let _result = cache.get_or_insert(hash, || Ok(DynAst::from(&ast)))?;
            // ast and _result go out of scope here
        }

        // The weak reference should be expired now, so this should compute a new value
        let mut computed = false;
        let ast2 = ctx.bvv_prim_with_size(42u64, 64)?;
        let _result = cache.get_or_insert(hash, || {
            computed = true;
            Ok(DynAst::from(&ast2))
        })?;

        assert!(
            computed,
            "Should have computed new value after weak ref expired"
        );
        Ok(())
    }

    // Test for collision detection mode
    #[test]
    #[cfg(feature = "panic-on-hash-collision")]
    #[should_panic(expected = "Hash collision detected")]
    fn test_hash_collision_detection_panics() {
        let ctx = crate::context::Context::new();
        let cache = AstCache::default();
        let hash = 777u64;

        // Insert first value
        let ast1 = ctx.bvv_prim_with_size(42u64, 64).unwrap();
        let _ = cache
            .get_or_insert(hash, || Ok(DynAst::from(&ast1)))
            .unwrap();

        // Try to insert different value with same hash - should panic
        let ast2 = ctx.bvv_prim_with_size(99u64, 64).unwrap();
        let _ = cache
            .get_or_insert(hash, || Ok(DynAst::from(&ast2)))
            .unwrap();
    }

    #[test]
    #[cfg(feature = "panic-on-hash-collision")]
    fn test_hash_collision_same_value_ok() -> Result<(), ClarirsError> {
        let ctx = crate::context::Context::new();
        let cache = AstCache::default();
        let hash = 888u64;

        // Insert first value
        let ast1 = ctx.bvv_prim_with_size(42u64, 64)?;
        let result1 = cache.get_or_insert(hash, || Ok(DynAst::from(&ast1)))?;

        // Insert same value with same hash - should be fine
        let ast2 = ctx.bvv_prim_with_size(42u64, 64)?;
        let result2 = cache.get_or_insert(hash, || Ok(DynAst::from(&ast2)))?;

        assert_eq!(result1, result2);
        Ok(())
    }

    #[test]
    #[cfg(feature = "panic-on-hash-collision")]
    fn test_always_computes_in_collision_mode() {
        let ctx = crate::context::Context::new();
        let cache = AstCache::default();
        let hash = 999u64;

        // Insert first value
        let ast1 = ctx.bvv_prim_with_size(42u64, 64).unwrap();
        let _ = cache
            .get_or_insert(hash, || Ok(DynAst::from(&ast1)))
            .unwrap();

        // This should always compute, even though the value is in cache
        let mut computed = false;
        let ast2 = ctx.bvv_prim_with_size(42u64, 64).unwrap();
        let _ = cache
            .get_or_insert(hash, || {
                computed = true;
                Ok(DynAst::from(&ast2))
            })
            .unwrap();

        assert!(
            computed,
            "Should always compute in collision detection mode"
        );
    }

    #[test]
    fn test_generic_cache_basic() {
        let cache = GenericCache::<u64, String>::default();

        let result1 = cache.get_or_insert(1, || Ok("hello".to_string())).unwrap();
        let result2 = cache
            .get_or_insert(1, || panic!("Should not compute when cached"))
            .unwrap();

        assert_eq!(result1, result2);
    }
}
