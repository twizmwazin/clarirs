//! Bitvector-flavored aliases and helpers over the unified [`AstOp`]/[`AstRef`].
//!
//! These extension traits provide `size()`/`sort()` for ops and nodes.

use crate::prelude::*;

/// Provides `size()` for ops and ASTs of bitvector sort. The width is derived
/// from the node's cached [`AstType`](super::op::AstType), so this is O(1) for
/// nodes (and O(1)/O(n) inference for a bare op).
pub trait BitVecOpExt<'c> {
    fn size(&self) -> u32;
}

impl<'c> BitVecOpExt<'c> for AstOp<'c> {
    fn size(&self) -> u32 {
        self.infer_type().size()
    }
}

impl<'c> BitVecOpExt<'c> for AstRef<'c> {
    fn size(&self) -> u32 {
        self.ty().size()
    }
}

pub trait BitVecAstExt<'c> {
    /// Chop the BV into `bits` sized pieces. Returns in little-endian order.
    fn chop(&self, bits: u32) -> Result<Vec<AstRef<'c>>, ClarirsError>;
}

impl<'c> BitVecAstExt<'c> for AstRef<'c> {
    fn chop(&self, bits: u32) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        if self.size() % bits != 0 {
            return Err(ClarirsError::InvalidChopSize {
                size: self.size(),
                bits,
            });
        }

        let mut res = vec![];
        for i in 0..self.size() / bits {
            res.push(
                self.context()
                    .extract(self, ((i + 1) * bits) - 1, i * bits)?,
            );
        }
        res.reverse();

        Ok(res)
    }
}
