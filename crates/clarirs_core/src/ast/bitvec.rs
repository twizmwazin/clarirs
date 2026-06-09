//! Bitvector-flavored aliases and helpers over the unified [`AstOp`]/[`AstRef`].
//!
//! `BitVecOp` and `BitVecAst` are aliases for the single op enum and node
//! reference; they are kept for readability and to preserve existing import
//! paths.

pub use super::node::BitVecAst;
pub use super::op::AstOp as BitVecOp;

use crate::prelude::*;

/// Provides `size()` for ops and ASTs of bitvector sort. The width is derived
/// from the node's cached [`AstType`](super::op::AstType), so this is O(1) for
/// nodes (and O(1)/O(n) inference for a bare op).
pub trait BitVecOpExt<'c> {
    fn size(&self) -> u32;
}

impl<'c> BitVecOpExt<'c> for BitVecOp<'c> {
    fn size(&self) -> u32 {
        self.infer_type().size()
    }
}

impl<'c> BitVecOpExt<'c> for BitVecAst<'c> {
    fn size(&self) -> u32 {
        self.ty().size()
    }
}

pub trait BitVecAstExt<'c> {
    /// Chop the BV into `bits` sized pieces. Returns in little-endian order.
    fn chop(&self, bits: u32) -> Result<Vec<BitVecAst<'c>>, ClarirsError>;
}

impl<'c> BitVecAstExt<'c> for BitVecAst<'c> {
    fn chop(&self, bits: u32) -> Result<Vec<BitVecAst<'c>>, ClarirsError> {
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
