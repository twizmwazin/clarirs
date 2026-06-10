//! Float-flavored aliases and helpers over the unified [`AstOp`]/[`AstRef`].
//!
//! These extension traits provide `size()`/`sort()` for ops and nodes.

use crate::prelude::*;

/// Provides `size()` (total IEEE bit width) for float ops and ASTs.
pub trait FloatExt<'c> {
    fn size(&self) -> u32;
}

impl<'c> FloatExt<'c> for AstOp<'c> {
    fn size(&self) -> u32 {
        self.infer_type().size()
    }
}

impl<'c> FloatExt<'c> for AstRef<'c> {
    fn size(&self) -> u32 {
        self.ty().size()
    }
}

/// Provides `sort()` for float ops and ASTs.
pub trait FloatOpExt<'c> {
    fn sort(&self) -> FSort;
}

impl<'c> FloatOpExt<'c> for AstOp<'c> {
    fn sort(&self) -> FSort {
        self.infer_type().fsort().unwrap_or_else(FSort::f64)
    }
}

impl<'c> FloatOpExt<'c> for AstRef<'c> {
    fn sort(&self) -> FSort {
        self.ty().fsort().unwrap_or_else(FSort::f64)
    }
}
