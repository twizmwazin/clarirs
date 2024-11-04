use std::sync::{RwLock, Weak};

use ahash::HashMap;

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
    pub fn get_or_insert_with_bool<F: FnOnce() -> BoolAst<'c>>(
        &self,
        hash: u64,
        f: F,
    ) -> BoolAst<'c> {
        let mut inner = self.inner.write().unwrap();
        match inner.get(&hash).and_then(|v| v.as_bool()) {
            Some(value) => value,
            None => {
                let this = f();
                inner.insert(hash, this.clone().into());
                this
            }
        }
    }

    pub fn get_or_insert_with_bv<F: FnOnce() -> BitVecAst<'c>>(
        &self,
        hash: u64,
        f: F,
    ) -> BitVecAst<'c> {
        let mut inner = self.inner.write().unwrap();
        match inner.get(&hash).and_then(|v| v.as_bv()) {
            Some(value) => value,
            None => {
                let this = f();
                inner.insert(hash, this.clone().into());
                this
            }
        }
    }

    pub fn get_or_insert_with_float<F: FnOnce() -> FloatAst<'c>>(
        &self,
        hash: u64,
        f: F,
    ) -> FloatAst<'c> {
        let mut inner = self.inner.write().unwrap();
        match inner.get(&hash).and_then(|v| v.as_float()) {
            Some(value) => value,
            None => {
                let this = f();
                inner.insert(hash, this.clone().into());
                this
            }
        }
    }

    pub fn get_or_insert_with_string<F: FnOnce() -> StringAst<'c>>(
        &self,
        hash: u64,
        f: F,
    ) -> StringAst<'c> {
        let mut inner = self.inner.write().unwrap();
        match inner.get(&hash).and_then(|v| v.as_string()) {
            Some(value) => value,
            None => {
                let this = f();
                inner.insert(hash, this.clone().into());
                this
            }
        }
    }
}
