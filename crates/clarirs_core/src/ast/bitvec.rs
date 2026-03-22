use crate::prelude::*;

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
