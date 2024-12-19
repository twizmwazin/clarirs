use std::sync::{Arc, RwLock, Weak};

use ahash::HashMap;

use crate::prelude::*;

#[derive(Debug)]
enum AstCacheValue<'c> {
    Boolean(Weak<AstNode<'c, BooleanOp<'c>>>),
    BitVec(Weak<AstNode<'c, BitVecOp<'c>>>),
    Float(Weak<AstNode<'c, FloatOp<'c>>>),
    String(Weak<AstNode<'c, StringOp<'c>>>),
}

#[allow(dead_code)]
impl<'c> AstCacheValue<'c> {
    fn as_bool(&self) -> Option<BoolAst<'c>> {
        match self {
            AstCacheValue::Boolean(weak) => weak.upgrade(),
            _ => None,
        }
    }

    fn as_bv(&self) -> Option<BitVecAst<'c>> {
        match self {
            AstCacheValue::BitVec(weak) => weak.upgrade(),
            _ => None,
        }
    }

    fn as_float(&self) -> Option<FloatAst<'c>> {
        match self {
            AstCacheValue::Float(weak) => weak.upgrade(),
            _ => None,
        }
    }

    fn as_string(&self) -> Option<StringAst<'c>> {
        match self {
            AstCacheValue::String(weak) => weak.upgrade(),
            _ => None,
        }
    }
}

impl<'c> From<BoolAst<'c>> for AstCacheValue<'c> {
    fn from(ast: BoolAst<'c>) -> Self {
        AstCacheValue::Boolean(BoolAst::downgrade(&ast))
    }
}

impl<'c> From<BitVecAst<'c>> for AstCacheValue<'c> {
    fn from(ast: BitVecAst<'c>) -> Self {
        AstCacheValue::BitVec(BitVecAst::downgrade(&ast))
    }
}

impl<'c> From<FloatAst<'c>> for AstCacheValue<'c> {
    fn from(ast: FloatAst<'c>) -> Self {
        AstCacheValue::Float(FloatAst::downgrade(&ast))
    }
}

impl<'c> From<StringAst<'c>> for AstCacheValue<'c> {
    fn from(ast: StringAst<'c>) -> Self {
        AstCacheValue::String(StringAst::downgrade(&ast))
    }
}

#[derive(Debug, Default)]
pub struct AstCache<'c> {
    inner: RwLock<HashMap<u64, AstCacheValue<'c>>>,
}

impl<'c> AstCache<'c> {
    pub fn print_cache(&self) {
        let inner = self.inner.read().unwrap();

        for (hash, value) in inner.iter() {
            match value {
                AstCacheValue::Boolean(weak) => {
                    if let Some(strong) = weak.upgrade() {
                        println!("Hash: {:?}, Type: Boolean, Value: {:?}", hash, strong);
                    } else {
                        println!("Hash: {:?}, Type: Boolean, Value: <dropped>", hash);
                    }
                }
                AstCacheValue::BitVec(weak) => {
                    if let Some(strong) = weak.upgrade() {
                        println!("Hash: {:?}, Type: BitVec, Value: {:?}", hash, strong);
                    } else {
                        println!("Hash: {:?}, Type: BitVec, Value: <dropped>", hash);
                    }
                }
                AstCacheValue::Float(weak) => {
                    if let Some(strong) = weak.upgrade() {
                        println!("Hash: {:?}, Type: Float, Value: {:?}", hash, strong);
                    } else {
                        println!("Hash: {:?}, Type: Float, Value: <dropped>", hash);
                    }
                }
                AstCacheValue::String(weak) => {
                    if let Some(strong) = weak.upgrade() {
                        println!("Hash: {:?}, Type: String, Value: {:?}", hash, strong);
                    } else {
                        println!("Hash: {:?}, Type: String, Value: <dropped>", hash);
                    }
                }
            }
        }
    }

    pub fn get_or_insert_with_bool<F>(&self, hash: u64, f: F) -> Result<BoolAst<'c>, ClarirsError>
    where
        F: FnOnce() -> Result<BoolAst<'c>, ClarirsError>,
    {
        // Step 1: Try to get a read lock and check if the value is already in the cache
        {
            let inner = self.inner.read().unwrap();
            if let Some(AstCacheValue::Boolean(weak)) = inner.get(&hash) {
                if let Some(arc) = weak.upgrade() {
                    return Ok(arc);
                }
            }
            // Value not found or expired; we'll compute it next
        } // Read lock is dropped here

        // Step 2: Compute the value without holding any lock
        let arc = f()?; // This may call `simplify()` and recurse

        // Step 3: Acquire a write lock to insert the new value
        let mut inner = self.inner.write().unwrap();

        // Step 4: Check again if the value was inserted while we were computing
        let entry = inner
            .entry(hash)
            .or_insert_with(|| AstCacheValue::Boolean(Weak::new()));

        match entry {
            AstCacheValue::Boolean(weak) => {
                if let Some(existing_arc) = weak.upgrade() {
                    Ok(existing_arc)
                } else {
                    // Step 5: Insert the new value into the cache
                    *entry = AstCacheValue::Boolean(Arc::downgrade(&arc));
                    Ok(arc)
                }
            }
            _ => unreachable!(),
        }
    }

    pub fn get_or_insert_with_bv<F>(&self, hash: u64, f: F) -> Result<BitVecAst<'c>, ClarirsError>
    where
        F: FnOnce() -> Result<BitVecAst<'c>, ClarirsError>,
    {
        // Step 1: Try to get a read lock and check if the value is already in the cache
        {
            let inner = self.inner.read().unwrap();
            if let Some(AstCacheValue::BitVec(weak)) = inner.get(&hash) {
                if let Some(arc) = weak.upgrade() {
                    return Ok(arc);
                }
            }
            // Value not found or expired; we'll compute it next
        } // Read lock is dropped here

        // Step 2: Compute the value without holding any lock
        let arc = f()?; // This may call `simplify()` and recurse

        // Step 3: Acquire a write lock to insert the new value
        let mut inner = self.inner.write().unwrap();

        // Step 4: Check again if the value was inserted while we were computing
        let entry = inner
            .entry(hash)
            .or_insert_with(|| AstCacheValue::BitVec(Weak::new()));

        match entry {
            AstCacheValue::BitVec(weak) => {
                if let Some(existing_arc) = weak.upgrade() {
                    Ok(existing_arc)
                } else {
                    // Step 5: Insert the new value into the cache
                    *entry = AstCacheValue::BitVec(Arc::downgrade(&arc));
                    Ok(arc)
                }
            }
            _ => unreachable!(),
        }
    }

    pub fn get_or_insert_with_float<F>(&self, hash: u64, f: F) -> Result<FloatAst<'c>, ClarirsError>
    where
        F: FnOnce() -> Result<FloatAst<'c>, ClarirsError>,
    {
        // Step 1: Try to get a read lock and check if the value is already in the cache
        {
            let inner = self.inner.read().unwrap();
            if let Some(AstCacheValue::Float(weak)) = inner.get(&hash) {
                if let Some(arc) = weak.upgrade() {
                    return Ok(arc);
                }
            }
            // Value not found or expired; we'll compute it next
        } // Read lock is dropped here

        // Step 2: Compute the value without holding any lock
        let arc = f()?; // This may call `simplify()` and recurse

        // Step 3: Acquire a write lock to insert the new value
        let mut inner = self.inner.write().unwrap();

        // Step 4: Check again if the value was inserted while we were computing
        let entry = inner
            .entry(hash)
            .or_insert_with(|| AstCacheValue::Float(Weak::new()));

        match entry {
            AstCacheValue::Float(weak) => {
                if let Some(existing_arc) = weak.upgrade() {
                    Ok(existing_arc)
                } else {
                    // Step 5: Insert the new value into the cache
                    *entry = AstCacheValue::Float(Arc::downgrade(&arc));
                    Ok(arc)
                }
            }
            _ => unreachable!(),
        }
    }

    pub fn get_or_insert_with_string<F>(
        &self,
        hash: u64,
        f: F,
    ) -> Result<StringAst<'c>, ClarirsError>
    where
        F: FnOnce() -> Result<StringAst<'c>, ClarirsError>,
    {
        // Step 1: Try to get a read lock and check if the value is already in the cache
        {
            let inner = self.inner.read().unwrap();
            if let Some(AstCacheValue::String(weak)) = inner.get(&hash) {
                if let Some(arc) = weak.upgrade() {
                    return Ok(arc);
                }
            }
            // Value not found or expired; we'll compute it next
        } // Read lock is dropped here

        // Step 2: Compute the value without holding any lock
        let arc = f()?; // This may call `simplify()` and recurse

        // Step 3: Acquire a write lock to insert the new value
        let mut inner = self.inner.write().unwrap();

        // Step 4: Check again if the value was inserted while we were computing
        let entry = inner
            .entry(hash)
            .or_insert_with(|| AstCacheValue::String(Weak::new()));

        match entry {
            AstCacheValue::String(weak) => {
                if let Some(existing_arc) = weak.upgrade() {
                    Ok(existing_arc)
                } else {
                    // Step 5: Insert the new value into the cache
                    *entry = AstCacheValue::String(Arc::downgrade(&arc));
                    Ok(arc)
                }
            }
            _ => unreachable!(),
        }
    }
}
