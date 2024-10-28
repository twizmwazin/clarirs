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

#[derive(Debug, Default)]
pub struct AstCache<'c> {
    inner: RwLock<HashMap<u64, AstCacheValue<'c>>>,
}

impl<'c> AstCache<'c> {
    pub fn get_or_insert_with_bool<F: FnOnce() -> BoolAst<'c>>(
        &self,
        hash: u64,
        f: F,
    ) -> BoolAst<'c> {
        let mut inner = self.inner.write().unwrap();
        let entry = inner
            .entry(hash)
            .or_insert_with(|| AstCacheValue::Boolean(Weak::new()));
        match entry {
            AstCacheValue::Boolean(weak) => {
                if let Some(arc) = weak.upgrade() {
                    arc
                } else {
                    let arc = f();
                    *entry = AstCacheValue::Boolean(Arc::downgrade(&arc));
                    arc
                }
            }
            _ => unreachable!(),
        }
    }

    pub fn get_or_insert_with_bv<F: FnOnce() -> BitVecAst<'c>>(
        &self,
        hash: u64,
        f: F,
    ) -> BitVecAst<'c> {
        let mut inner = self.inner.write().unwrap();
        let entry = inner
            .entry(hash)
            .or_insert_with(|| AstCacheValue::BitVec(Weak::new()));
        match entry {
            AstCacheValue::BitVec(weak) => {
                if let Some(arc) = weak.upgrade() {
                    arc
                } else {
                    let arc = f();
                    *entry = AstCacheValue::BitVec(Arc::downgrade(&arc));
                    arc
                }
            }
            _ => unreachable!(),
        }
    }

    pub fn get_or_insert_with_float<F: FnOnce() -> FloatAst<'c>>(
        &self,
        hash: u64,
        f: F,
    ) -> FloatAst<'c> {
        let mut inner = self.inner.write().unwrap();
        let entry = inner
            .entry(hash)
            .or_insert_with(|| AstCacheValue::Float(Weak::new()));
        match entry {
            AstCacheValue::Float(weak) => {
                if let Some(arc) = weak.upgrade() {
                    arc
                } else {
                    let arc = f();
                    *entry = AstCacheValue::Float(Arc::downgrade(&arc));
                    arc
                }
            }
            _ => unreachable!(),
        }
    }

    pub fn get_or_insert_with_string<F: FnOnce() -> StringAst<'c>>(
        &self,
        hash: u64,
        f: F,
    ) -> StringAst<'c> {
        let mut inner = self.inner.write().unwrap();
        let entry = inner
            .entry(hash)
            .or_insert_with(|| AstCacheValue::String(Weak::new()));
        match entry {
            AstCacheValue::String(weak) => {
                if let Some(arc) = weak.upgrade() {
                    arc
                } else {
                    let arc = f();
                    *entry = AstCacheValue::String(Arc::downgrade(&arc));
                    arc
                }
            }
            _ => unreachable!(),
        }
    }
}
