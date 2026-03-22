use ahash::HashMap;
use std::{
    hash::Hash,
    sync::{Arc, RwLock, Weak},
};

use crate::prelude::*;

/// A trait for caching values based on a key. In the context of clarirs, this
/// is used to cache ASTs, as well as the results of various algorithms.
/// The `get_or_insert` method will either return the cached value or compute
/// a new value and insert it into the cache.
pub trait Cache<K, V> {
    fn get_or_insert<E>(&self, key: K, value_cv: impl FnMut() -> Result<V, E>) -> Result<V, E>;

    fn drop(&self, key: K);
}

impl<K, V> Cache<K, V> for () {
    fn get_or_insert<E>(&self, _: K, mut value_cv: impl FnMut() -> Result<V, E>) -> Result<V, E> {
        value_cv()
    }

    fn drop(&self, _key: K) {
        // No-op
    }
}

/// A generic cache implementation that uses a `HashMap` to store key-value pairs.
#[derive(Debug)]
pub struct GenericCache<K, V>(RwLock<HashMap<K, V>>);

impl<K, V> Default for GenericCache<K, V> {
    fn default() -> Self {
        Self(RwLock::new(HashMap::default()))
    }
}

impl<K: Hash + Eq, V: Clone> Cache<K, V> for GenericCache<K, V> {
    fn get_or_insert<E>(&self, key: K, mut value_cv: impl FnMut() -> Result<V, E>) -> Result<V, E> {
        // Fast path: check with read lock
        {
            let locked = self.0.read().unwrap();
            if let Some(value) = locked.get(&key) {
                return Ok(value.clone());
            }
        }
        // Slow path: compute and insert with write lock
        let mut locked = self.0.write().unwrap();
        // Double-check after acquiring write lock
        if let Some(value) = locked.get(&key) {
            return Ok(value.clone());
        }
        let value = value_cv()?;
        locked.insert(key, value.clone());
        Ok(value)
    }

    fn drop(&self, key: K) {
        let mut locked = self.0.write().unwrap();
        locked.remove(&key);
    }
}

/// A special cache for when the result type is an AST. Unlike the generic cache,
/// this cache stores weak references to the AST nodes.
#[derive(Debug, Default)]
pub struct AstCache<'c>(RwLock<HashMap<u64, Weak<AstNode<'c>>>>);

impl<'c> Cache<u64, AstRef<'c>> for AstCache<'c> {
    fn get_or_insert<E>(
        &self,
        hash: u64,
        f: impl FnOnce() -> Result<AstRef<'c>, E>,
    ) -> Result<AstRef<'c>, E> {
        #[cfg(not(feature = "panic-on-hash-collision"))]
        {
            // Normal mode: Try to get from cache first, compute only if needed
            {
                let inner = self.0.read().unwrap();
                if let Some(weak) = inner.get(&hash)
                    && let Some(arc) = weak.upgrade()
                {
                    return Ok(arc);
                }
            }

            let arc = f()?;

            let mut inner = self.0.write().unwrap();
            inner.insert(hash, Arc::downgrade(&arc));

            Ok(arc)
        }

        #[cfg(feature = "panic-on-hash-collision")]
        {
            let arc = f()?;

            let mut inner = self.0.write().unwrap();

            if let Some(existing_weak) = inner.get(&hash)
                && let Some(existing_arc) = existing_weak.upgrade()
                && *existing_arc != *arc
            {
                panic!(
                    "Hash collision detected! Hash: {hash}, Existing: {existing_arc:?}, New: {arc:?}"
                );
            }

            inner.insert(hash, Arc::downgrade(&arc));

            Ok(arc)
        }
    }

    fn drop(&self, key: u64) {
        let mut locked = self.0.write().unwrap();
        locked.remove(&key);
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

        let ast1 = ctx.bvv_prim_with_size(42u64, 64)?;
        let hash1 = 12345u64;

        let result1 = cache.get_or_insert::<ClarirsError>(hash1, || Ok(ast1.clone()))?;

        let result2 = cache.get_or_insert::<ClarirsError>(hash1, || {
            panic!("Should not compute new value when cached")
        })?;
        assert_eq!(result1, result2);
        Ok(())
    }

    #[test]
    #[cfg(feature = "panic-on-hash-collision")]
    fn test_ast_cache_basic_collision_mode() -> Result<(), ClarirsError> {
        let ctx = crate::context::Context::new();
        let cache = AstCache::default();

        let ast1 = ctx.bvv_prim_with_size(42u64, 64)?;
        let hash1 = 12345u64;

        let result1 = cache.get_or_insert::<ClarirsError>(hash1, || Ok(ast1.clone()))?;

        let ast2 = ctx.bvv_prim_with_size(42u64, 64)?;
        let result2 = cache.get_or_insert::<ClarirsError>(hash1, || Ok(ast2.clone()))?;
        assert_eq!(result1, result2);
        Ok(())
    }

    #[test]
    fn test_ast_cache_different_hashes() -> Result<(), ClarirsError> {
        let ctx = crate::context::Context::new();
        let cache = AstCache::default();

        let ast1 = ctx.bvv_prim_with_size(42u64, 64)?;
        let ast2 = ctx.bvv_prim_with_size(99u64, 64)?;

        let result1 = cache.get_or_insert::<ClarirsError>(1, || Ok(ast1.clone()))?;
        let result2 = cache.get_or_insert::<ClarirsError>(2, || Ok(ast2.clone()))?;

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
            let ast = ctx.bvv_prim_with_size(42u64, 64)?;
            let _result = cache.get_or_insert::<ClarirsError>(hash, || Ok(ast.clone()))?;
        }

        let mut computed = false;
        let ast2 = ctx.bvv_prim_with_size(42u64, 64)?;
        let _result = cache.get_or_insert::<ClarirsError>(hash, || {
            computed = true;
            Ok(ast2.clone())
        })?;

        assert!(
            computed,
            "Should have computed new value after weak ref expired"
        );
        Ok(())
    }

    #[test]
    #[cfg(feature = "panic-on-hash-collision")]
    #[should_panic(expected = "Hash collision detected")]
    fn test_hash_collision_detection_panics() {
        let ctx = crate::context::Context::new();
        let cache = AstCache::default();
        let hash = 777u64;

        let ast1 = ctx.bvv_prim_with_size(42u64, 64).unwrap();
        let _ = cache
            .get_or_insert::<ClarirsError>(hash, || Ok(ast1.clone()))
            .unwrap();

        let ast2 = ctx.bvv_prim_with_size(99u64, 64).unwrap();
        let _ = cache
            .get_or_insert::<ClarirsError>(hash, || Ok(ast2.clone()))
            .unwrap();
    }

    #[test]
    #[cfg(feature = "panic-on-hash-collision")]
    fn test_hash_collision_same_value_ok() -> Result<(), ClarirsError> {
        let ctx = crate::context::Context::new();
        let cache = AstCache::default();
        let hash = 888u64;

        let ast1 = ctx.bvv_prim_with_size(42u64, 64)?;
        let result1 = cache.get_or_insert::<ClarirsError>(hash, || Ok(ast1.clone()))?;

        let ast2 = ctx.bvv_prim_with_size(42u64, 64)?;
        let result2 = cache.get_or_insert::<ClarirsError>(hash, || Ok(ast2.clone()))?;

        assert_eq!(result1, result2);
        Ok(())
    }

    #[test]
    #[cfg(feature = "panic-on-hash-collision")]
    fn test_always_computes_in_collision_mode() {
        let ctx = crate::context::Context::new();
        let cache = AstCache::default();
        let hash = 999u64;

        let ast1 = ctx.bvv_prim_with_size(42u64, 64).unwrap();
        let _ = cache
            .get_or_insert::<ClarirsError>(hash, || Ok(ast1.clone()))
            .unwrap();

        let mut computed = false;
        let ast2 = ctx.bvv_prim_with_size(42u64, 64).unwrap();
        let _ = cache
            .get_or_insert::<ClarirsError>(hash, || {
                computed = true;
                Ok(ast2.clone())
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

        let result1 = cache
            .get_or_insert::<ClarirsError>(1, || Ok("hello".to_string()))
            .unwrap();
        let result2 = cache
            .get_or_insert::<ClarirsError>(1, || panic!("Should not compute when cached"))
            .unwrap();

        assert_eq!(result1, result2);
    }
}
