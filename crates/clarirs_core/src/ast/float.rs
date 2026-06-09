//! Float-flavored aliases and helpers over the unified [`AstOp`]/[`AstRef`].
//!
//! `FloatOp` and `FloatAst` are aliases for the single op enum and node
//! reference; they are kept for readability and to preserve existing import
//! paths.

pub use super::node::FloatAst;
pub use super::op::AstOp as FloatOp;

use crate::prelude::*;

/// Provides `size()` (total IEEE bit width) for float ops and ASTs.
pub trait FloatExt<'c> {
    fn size(&self) -> u32;
}

impl<'c> FloatExt<'c> for FloatOp<'c> {
    fn size(&self) -> u32 {
        self.infer_type().size()
    }
}

impl<'c> FloatExt<'c> for FloatAst<'c> {
    fn size(&self) -> u32 {
        self.ty().size()
    }
}

/// Provides `sort()` for float ops and ASTs.
pub trait FloatOpExt<'c> {
    fn sort(&self) -> FSort;
}

impl<'c> FloatOpExt<'c> for FloatOp<'c> {
    fn sort(&self) -> FSort {
        self.infer_type().fsort().unwrap_or_else(FSort::f64)
    }
}

impl<'c> FloatOpExt<'c> for FloatAst<'c> {
    fn sort(&self) -> FSort {
        self.ty().fsort().unwrap_or_else(FSort::f64)
    }
}
