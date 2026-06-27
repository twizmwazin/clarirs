use ahash::HashMap;
use std::{
    hash::Hash,
    sync::{Arc, RwLock, Weak},
};

use crate::prelude::*;

/// The main AST interning cache: a structural-hash directory of live nodes.
/// Construction resolves-or-inserts through it, and inline result cells on
/// [`AstNode`] resolve their stored hashes through it.
pub trait AstCache<'c> {
    /// Resolve a hash to its interned, still-live node, if any.
    fn get(&self, hash: u64) -> Option<AstRef<'c>>;

    /// Intern `node` under `hash`.
    fn insert(&self, hash: u64, node: &AstRef<'c>);

    /// Remove the entry for `hash` (used when a node is dropped).
    fn drop(&self, hash: u64);

    /// Resolve `hash`, or build a node, intern it, and return it on miss.
    fn get_or_insert<E>(
        &self,
        hash: u64,
        build: impl FnOnce() -> Result<AstRef<'c>, E>,
    ) -> Result<AstRef<'c>, E> {
        if let Some(node) = self.get(hash) {
            return Ok(node);
        }
        let node = build()?;
        self.insert(hash, &node);
        Ok(node)
    }
}

/// Weak-reference-backed [`AstCache`]; nodes are held weakly and prune their own
/// entry on drop.
#[derive(Debug, Default)]
pub struct WeakAstCache<'c>(RwLock<HashMap<u64, Weak<AstNode<'c>>>>);

impl<'c> AstCache<'c> for WeakAstCache<'c> {
    fn get(&self, hash: u64) -> Option<AstRef<'c>> {
        self.0.read().unwrap().get(&hash).and_then(Weak::upgrade)
    }

    fn insert(&self, hash: u64, node: &AstRef<'c>) {
        let mut inner = self.0.write().unwrap();

        // A different live value under this hash means two distinct ASTs collide.
        #[cfg(feature = "panic-on-hash-collision")]
        if let Some(existing) = inner.get(&hash).and_then(Weak::upgrade)
            && existing != *node
        {
            panic!("Hash collision detected! Hash: {hash}, Existing: {existing:?}, New: {node:?}");
        }

        inner.insert(hash, Arc::downgrade(node));
    }

    fn drop(&self, hash: u64) {
        self.0.write().unwrap().remove(&hash);
    }

    // Collision detection must recompute and compare on every call, even a cache
    // hit, which the derived get-then-insert cannot express.
    #[cfg(feature = "panic-on-hash-collision")]
    fn get_or_insert<E>(
        &self,
        hash: u64,
        build: impl FnOnce() -> Result<AstRef<'c>, E>,
    ) -> Result<AstRef<'c>, E> {
        let arc = build()?;
        self.insert(hash, &arc);
        Ok(arc)
    }
}

/// A generic hash-map cache, used as an external post-order-walk memo by callers
/// that keep results in a standalone map rather than an inline cell.
#[derive(Debug)]
pub struct GenericCache<K, V>(RwLock<HashMap<K, V>>);

impl<K, V> Default for GenericCache<K, V> {
    fn default() -> Self {
        Self(RwLock::new(HashMap::default()))
    }
}

impl<K: Hash + Eq + Clone, V: Clone> GenericCache<K, V> {
    /// Probe the cache without computing a value on miss.
    pub fn get(&self, key: &K) -> Option<V> {
        self.0.read().unwrap().get(key).cloned()
    }

    pub fn insert(&self, key: K, value: &V) {
        self.0.write().unwrap().insert(key, value.clone());
    }

    pub fn get_or_insert<E>(
        &self,
        key: K,
        value_cv: impl FnOnce() -> Result<V, E>,
    ) -> Result<V, E> {
        if let Some(value) = self.get(&key) {
            return Ok(value);
        }
        let value = value_cv()?;
        self.insert(key, &value);
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(not(feature = "panic-on-hash-collision"))]
    fn test_ast_cache_basic() -> Result<(), ClarirsError> {
        let ctx = crate::context::Context::new();
        let cache = WeakAstCache::default();

        // Create a simple AST
        let ast1 = ctx.bvv(BitVec::from((42, 64)))?;
        let hash1 = 12345u64; // Arbitrary hash for testing

        // Insert into cache
        let result1 = cache.get_or_insert::<ClarirsError>(hash1, || Ok(ast1.clone()))?;

        // Verify we can retrieve it without recomputing
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
        let cache = WeakAstCache::default();

        // Create a simple AST
        let ast1 = ctx.bvv(BitVec::from((42, 64)))?;
        let hash1 = 12345u64; // Arbitrary hash for testing

        // Insert into cache
        let result1 = cache.get_or_insert::<ClarirsError>(hash1, || Ok(ast1.clone()))?;

        // In collision mode, it will always recompute, so provide a valid computation
        let ast2 = ctx.bvv(BitVec::from((42, 64)))?;
        let result2 = cache.get_or_insert::<ClarirsError>(hash1, || Ok(ast2.clone()))?;
        assert_eq!(result1, result2);
        Ok(())
    }

    #[test]
    fn test_ast_cache_different_hashes() -> Result<(), ClarirsError> {
        let ctx = crate::context::Context::new();
        let cache = WeakAstCache::default();

        let ast1 = ctx.bvv(BitVec::from((42, 64)))?;
        let ast2 = ctx.bvv(BitVec::from((99, 64)))?;

        let result1 = cache.get_or_insert::<ClarirsError>(1, || Ok(ast1.clone()))?;
        let result2 = cache.get_or_insert::<ClarirsError>(2, || Ok(ast2.clone()))?;

        // Different hashes should cache different values
        assert_ne!(result1, result2);
        Ok(())
    }

    #[test]
    #[cfg(not(feature = "panic-on-hash-collision"))]
    fn test_ast_cache_weak_reference_cleanup() -> Result<(), ClarirsError> {
        let ctx = crate::context::Context::new();
        let cache = WeakAstCache::default();
        let hash = 999u64;

        {
            // Create and cache an AST
            let ast = ctx.bvv(BitVec::from((42, 64)))?;
            let _result = cache.get_or_insert::<ClarirsError>(hash, || Ok(ast.clone()))?;
            // ast and _result go out of scope here
        }

        // The weak reference should be expired now, so this should compute a new value
        let mut computed = false;
        let ast2 = ctx.bvv(BitVec::from((42, 64)))?;
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

    // Test for collision detection mode
    #[test]
    #[cfg(feature = "panic-on-hash-collision")]
    #[should_panic(expected = "Hash collision detected")]
    fn test_hash_collision_detection_panics() {
        let ctx = crate::context::Context::new();
        let cache = WeakAstCache::default();
        let hash = 777u64;

        // Insert first value
        let ast1 = ctx.bvv(BitVec::from((42, 64))).unwrap();
        let _ = cache
            .get_or_insert::<ClarirsError>(hash, || Ok(ast1.clone()))
            .unwrap();

        // Try to insert different value with same hash - should panic
        let ast2 = ctx.bvv(BitVec::from((99, 64))).unwrap();
        let _ = cache
            .get_or_insert::<ClarirsError>(hash, || Ok(ast2.clone()))
            .unwrap();
    }

    #[test]
    #[cfg(feature = "panic-on-hash-collision")]
    fn test_hash_collision_same_value_ok() -> Result<(), ClarirsError> {
        let ctx = crate::context::Context::new();
        let cache = WeakAstCache::default();
        let hash = 888u64;

        // Insert first value
        let ast1 = ctx.bvv(BitVec::from((42, 64)))?;
        let result1 = cache.get_or_insert::<ClarirsError>(hash, || Ok(ast1.clone()))?;

        // Insert same value with same hash - should be fine
        let ast2 = ctx.bvv(BitVec::from((42, 64)))?;
        let result2 = cache.get_or_insert::<ClarirsError>(hash, || Ok(ast2.clone()))?;

        assert_eq!(result1, result2);
        Ok(())
    }

    #[test]
    #[cfg(feature = "panic-on-hash-collision")]
    fn test_always_computes_in_collision_mode() {
        let ctx = crate::context::Context::new();
        let cache = WeakAstCache::default();
        let hash = 999u64;

        // Insert first value
        let ast1 = ctx.bvv(BitVec::from((42, 64))).unwrap();
        let _ = cache
            .get_or_insert::<ClarirsError>(hash, || Ok(ast1.clone()))
            .unwrap();

        // This should always compute, even though the value is in cache
        let mut computed = false;
        let ast2 = ctx.bvv(BitVec::from((42, 64))).unwrap();
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
