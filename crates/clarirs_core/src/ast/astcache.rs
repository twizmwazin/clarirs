use std::sync::{Arc, Weak};

use dashmap::DashMap;

use crate::prelude::*;

#[derive(Debug)]
enum AstCacheValue<'c> {
    Boolean(Weak<AstNode<'c, BooleanOp<'c>>>),
    BitVec(Weak<AstNode<'c, BitVecOp<'c>>>),
    Float(Weak<AstNode<'c, FloatOp<'c>>>),
    String(Weak<AstNode<'c, StringOp<'c>>>),
}

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

#[derive(Debug, Default)]
pub struct AstCache<'c> {
    inner: DashMap<u64, AstCacheValue<'c>, ahash::RandomState>,
}

impl<'c> AstCache<'c> {
    pub fn get_or_insert_with_bool<F: FnOnce() -> BoolAst<'c>>(
        &self,
        hash: u64,
        f: F,
    ) -> BoolAst<'c> {
        match self.inner.get(&hash).and_then(|e| e.value().as_bool()) {
            Some(e) => e,
            None => {
                let this = f();
                self.inner
                    .insert(hash, AstCacheValue::Boolean(Arc::downgrade(&this)));
                this
            }
        }
    }

    pub fn get_or_insert_with_bv<F: FnOnce() -> BitVecAst<'c>>(
        &self,
        hash: u64,
        f: F,
    ) -> BitVecAst<'c> {
        match self.inner.get(&hash).and_then(|e| e.value().as_bv()) {
            Some(e) => e,
            None => {
                let this = f();
                self.inner
                    .insert(hash, AstCacheValue::BitVec(Arc::downgrade(&this)));
                this
            }
        }
    }

    pub fn get_or_insert_with_float<F: FnOnce() -> FloatAst<'c>>(
        &self,
        hash: u64,
        f: F,
    ) -> FloatAst<'c> {
        match self.inner.get(&hash).and_then(|e| e.value().as_float()) {
            Some(e) => e,
            None => {
                let this = f();
                self.inner
                    .insert(hash, AstCacheValue::Float(Arc::downgrade(&this)));
                this
            }
        }
    }

    pub fn get_or_insert_with_string<F: FnOnce() -> StringAst<'c>>(
        &self,
        hash: u64,
        f: F,
    ) -> StringAst<'c> {
        match self.inner.get(&hash).and_then(|e| e.value().as_string()) {
            Some(e) => e,
            None => {
                let this = f();
                self.inner
                    .insert(hash, AstCacheValue::String(Arc::downgrade(&this)));
                this
            }
        }
    }
}
