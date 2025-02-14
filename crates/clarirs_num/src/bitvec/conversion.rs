use num_bigint::BigUint;
use smallvec::SmallVec;
use std::convert::Infallible;
use std::convert::TryFrom;

use super::{BitVec, BitVecError};

impl TryFrom<i8> for BitVec {
    type Error = BitVecError;
    fn try_from(value: i8) -> Result<BitVec, BitVecError> {
        BitVec::new(SmallVec::from_slice(&[value as u64]), 8)
    }
}

impl TryFrom<u8> for BitVec {
    type Error = BitVecError;
    fn try_from(value: u8) -> Result<BitVec, BitVecError> {
        BitVec::new(SmallVec::from_slice(&[value as u64]), 8)
    }
}

impl TryFrom<i16> for BitVec {
    type Error = BitVecError;
    fn try_from(value: i16) -> Result<BitVec, BitVecError> {
        BitVec::new(SmallVec::from_slice(&[value as u64]), 16)
    }
}

impl TryFrom<u16> for BitVec {
    type Error = BitVecError;
    fn try_from(value: u16) -> Result<BitVec, BitVecError> {
        BitVec::new(SmallVec::from_slice(&[value as u64]), 16)
    }
}

impl TryFrom<i32> for BitVec {
    type Error = BitVecError;
    fn try_from(value: i32) -> Result<BitVec, BitVecError> {
        BitVec::new(SmallVec::from_slice(&[value as u64]), 32)
    }
}

impl TryFrom<u32> for BitVec {
    type Error = BitVecError;
    fn try_from(value: u32) -> Result<BitVec, BitVecError> {
        BitVec::new(SmallVec::from_slice(&[value as u64]), 32)
    }
}

impl TryFrom<i64> for BitVec {
    type Error = BitVecError;
    fn try_from(value: i64) -> Result<BitVec, BitVecError> {
        BitVec::new(
            SmallVec::from_slice(&[unsafe { std::mem::transmute::<i64, u64>(value) }]),
            64,
        )
    }
}

impl TryFrom<u64> for BitVec {
    type Error = BitVecError;
    fn try_from(value: u64) -> Result<BitVec, BitVecError> {
        BitVec::new(SmallVec::from_slice(&[value]), 64)
    }
}

impl TryFrom<i128> for BitVec {
    type Error = BitVecError;
    fn try_from(value: i128) -> Result<BitVec, BitVecError> {
        BitVec::new(
            SmallVec::from_slice(&[value as u64, (value >> 64) as u64]),
            128,
        )
    }
}

impl TryFrom<u128> for BitVec {
    type Error = BitVecError;
    fn try_from(value: u128) -> Result<BitVec, BitVecError> {
        BitVec::new(
            SmallVec::from_slice(&[value as u64, (value >> 64) as u64]),
            128,
        )
    }
}

impl TryFrom<BigUint> for BitVec {
    type Error = BitVecError;

    fn try_from(value: BigUint) -> Result<Self, Self::Error> {
        BitVec::from_biguint(&value, value.bits() as usize)
    }
}

impl TryFrom<&BitVec> for BigUint {
    type Error = Infallible; // `BigUint::from_bytes_be` never fails

    fn try_from(bv: &BitVec) -> Result<Self, Self::Error> {
        Ok(BigUint::from_bytes_be(
            bv.words
                .iter()
                .flat_map(|w| w.to_be_bytes())
                .collect::<Vec<u8>>()
                .as_slice(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use std::result::Result;

    use super::*;
    use num_traits::Zero;

    use crate::bitvec::BitVecError;

    #[test]
    fn test_to_biguint() -> Result<(), BitVecError> {
        use num_bigint::BigUint;
        use num_traits::One;

        // Test conversion of zero
        let bv = BitVec::zeros(64)?;
        assert_eq!(bv.to_biguint(), BigUint::zero());

        // Test various positive values
        let bv = BitVec::try_from(42u64)?;
        assert_eq!(bv.to_biguint(), BigUint::try_from(42u64)?);

        // Test different widths
        let bv = BitVec::try_from(0xFFu8)?;
        assert_eq!(bv.to_biguint(), BigUint::try_from(0xFFu64)?);

        let bv = BitVec::try_from(0xFFFFu16)?;
        assert_eq!(bv.to_biguint(), BigUint::try_from(0xFFFFu64)?);

        // Test maximum value for width
        let bv = BitVec::try_from(u32::MAX)?;
        assert_eq!(bv.to_biguint(), BigUint::try_from(u32::MAX)?);

        // Test odd-sized vectors (e.g., 17 bits)
        let value = BigUint::try_from(0x1FFFFu64)?; // 17 bits set
        let bv = BitVec::from_biguint(&value, 17).unwrap();
        assert_eq!(bv.to_biguint(), value);

        // Test single-bit vector
        let bv = BitVec::from_prim_with_size(1u8, 1)?;
        assert_eq!(bv.to_biguint(), BigUint::one());

        // Test zero-width vector
        let bv = BitVec::zeros(0)?;
        assert_eq!(bv.to_biguint(), BigUint::zero());

        // Test 72-bit vector
        let value = (BigUint::one() << 72u32) - BigUint::one(); // 2^72 - 1
        let bv = BitVec::from_biguint(&value, 72).unwrap();
        assert_eq!(bv.to_biguint(), value);

        Ok(())
    }

    #[test]
    fn test_from_biguint() -> Result<(), BitVecError> {
        use num_bigint::BigUint;
        use num_traits::One;

        // Test conversion try_from zero
        let bv = BitVec::from_biguint(&BigUint::zero(), 64).unwrap();
        assert_eq!(bv.to_u64().unwrap(), 0);

        // Test various positive values
        let value = BigUint::try_from(42u64)?;
        let bv = BitVec::from_biguint(&value, 64).unwrap();
        assert_eq!(bv.to_u64().unwrap(), 42);

        // Test value too large for width (should error)
        let value = BigUint::try_from(0xFFu64)?;
        assert!(BitVec::from_biguint(&value, 4).is_err());

        // Test truncation with from_biguint_trunc
        let value = BigUint::try_from(0xFFu64)?;
        let bv = BitVec::from_biguint_trunc(&value, 4);
        assert_eq!(bv.to_u64().unwrap() & 0xF, 0xF); // Only compare the lowest 4 bits

        // Test different widths
        let value = BigUint::try_from(0xFFu64)?;
        let bv = BitVec::from_biguint(&value, 8).unwrap();
        assert_eq!(bv.to_u64().unwrap(), 0xFF);

        // Test odd-sized vectors
        let value = BigUint::try_from(0x1Fu64)?; // 5 bits
        let bv = BitVec::from_biguint(&value, 5).unwrap();
        assert_eq!(bv.to_u64().unwrap(), 0x1F);

        // Test single-bit vector
        let bv = BitVec::from_biguint(&BigUint::one(), 1).unwrap();
        assert_eq!(bv.to_u64().unwrap(), 1);

        // Test zero-width vector
        let bv = BitVec::from_biguint(&BigUint::zero(), 0).unwrap();
        assert_eq!(bv.len(), 0);

        Ok(())
    }

    #[test]
    fn test_to_u64() -> Result<(), BitVecError> {
        // Test conversion of zero
        let bv = BitVec::zeros(64)?;
        assert_eq!(bv.to_u64().unwrap(), 0);

        // Test conversion of various values
        let bv = BitVec::try_from(42u64)?;
        assert_eq!(bv.to_u64().unwrap(), 42);

        // Test width > 64 (should error)
        let bv = BitVec::zeros(65)?;
        assert!(bv.to_u64().is_none());

        // Test different widths
        let bv = BitVec::try_from(0xFFu8)?;
        assert_eq!(bv.to_u64().unwrap(), 0xFF);

        let bv = BitVec::try_from(0xFFFFu16)?;
        assert_eq!(bv.to_u64().unwrap(), 0xFFFF);

        // Test maximum value for width
        let bv = BitVec::try_from(u32::MAX)?;
        assert_eq!(bv.to_u64().unwrap(), u32::MAX as u64);

        // Test odd-sized vectors
        let bv = BitVec::from_prim_with_size(0x1Fu8, 5)?; // 5 bits
        assert_eq!(bv.to_u64().unwrap(), 0x1F);

        // Test single-bit vector
        let bv = BitVec::from_prim_with_size(1u8, 1)?;
        assert_eq!(bv.to_u64().unwrap(), 1);

        Ok(())
    }

    #[test]
    fn test_to_usize() -> Result<(), BitVecError> {
        // Test conversion of zero
        let bv = BitVec::zeros(usize::BITS as usize)?;
        assert_eq!(bv.to_usize().unwrap(), 0);

        // Test conversion of various values
        let bv = BitVec::try_from(42u64)?;
        assert_eq!(bv.to_usize().unwrap(), 42);

        // Test width > usize::BITS (should error)
        let bv = BitVec::zeros((usize::BITS + 1) as usize)?;
        assert!(bv.to_usize().is_none());

        // Test different widths
        let bv = BitVec::try_from(0xFFu8)?;
        assert_eq!(bv.to_usize().unwrap(), 0xFF);

        let bv = BitVec::try_from(0xFFFFu16)?;
        assert_eq!(bv.to_usize().unwrap(), 0xFFFF);

        // Test maximum value for width
        let max_32bit = BitVec::try_from(u32::MAX)?;
        if usize::BITS >= 32 {
            assert_eq!(max_32bit.to_usize().unwrap(), u32::MAX as usize);
        } else {
            assert!(max_32bit.to_usize().is_none());
        }

        // Test odd-sized vectors
        let bv = BitVec::from_prim_with_size(0x1Fu8, 5)?; // 5 bits
        assert_eq!(bv.to_usize().unwrap(), 0x1F);

        // Test single-bit vector
        let bv = BitVec::from_prim_with_size(1u8, 1)?;
        assert_eq!(bv.to_usize().unwrap(), 1);

        Ok(())
    }

    #[test]
    fn test_from_u8() -> Result<(), BitVecError> {
        let bv = BitVec::try_from(42u8)?;
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.to_u64().unwrap(), 42);

        let bv = BitVec::try_from(0u8)?;
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.to_u64().unwrap(), 0);

        let bv = BitVec::try_from(255u8)?;
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.to_u64().unwrap(), 255);

        Ok(())
    }

    #[test]
    fn test_from_u16() -> Result<(), BitVecError> {
        let bv = BitVec::try_from(4242u16)?;
        assert_eq!(bv.len(), 16);
        assert_eq!(bv.to_u64().unwrap(), 4242);

        let bv = BitVec::try_from(0u16)?;
        assert_eq!(bv.len(), 16);
        assert_eq!(bv.to_u64().unwrap(), 0);

        let bv = BitVec::try_from(u16::MAX)?;
        assert_eq!(bv.len(), 16);
        assert_eq!(bv.to_u64().unwrap(), u16::MAX as u64);

        Ok(())
    }

    #[test]
    fn test_from_u32() -> Result<(), BitVecError> {
        let bv = BitVec::try_from(424242u32)?;
        assert_eq!(bv.len(), 32);
        assert_eq!(bv.to_u64().unwrap(), 424242);

        let bv = BitVec::try_from(0u32)?;
        assert_eq!(bv.len(), 32);
        assert_eq!(bv.to_u64().unwrap(), 0);

        let bv = BitVec::try_from(u32::MAX)?;
        assert_eq!(bv.len(), 32);
        assert_eq!(bv.to_u64().unwrap(), u32::MAX as u64);

        Ok(())
    }

    #[test]
    fn test_from_u64() -> Result<(), BitVecError> {
        let bv = BitVec::try_from(42424242u64)?;
        assert_eq!(bv.len(), 64);
        assert_eq!(bv.to_u64().unwrap(), 42424242);

        let bv = BitVec::try_from(0u64)?;
        assert_eq!(bv.len(), 64);
        assert_eq!(bv.to_u64().unwrap(), 0);

        let bv = BitVec::try_from(u64::MAX)?;
        assert_eq!(bv.len(), 64);
        assert_eq!(bv.to_u64().unwrap(), u64::MAX);

        Ok(())
    }

    #[test]
    fn test_from_u128() -> Result<(), BitVecError> {
        let bv = BitVec::try_from(4242424242424242u128)?;
        assert_eq!(bv.len(), 128);
        assert!(bv.to_u64().is_none()); // Too large for u64
        assert_eq!(
            bv.to_biguint(),
            num_bigint::BigUint::try_from(4242424242424242u128)?
        );

        let bv = BitVec::try_from(0u128)?;
        assert_eq!(bv.len(), 128);
        assert!(bv.to_u64().is_none()); // Even 0 should return None for 128-bit vectors

        let bv = BitVec::try_from(u128::MAX)?;
        assert_eq!(bv.len(), 128);
        assert!(bv.to_u64().is_none());
        assert_eq!(bv.to_biguint(), num_bigint::BigUint::try_from(u128::MAX)?);

        Ok(())
    }

    #[test]
    fn test_from_i8() -> Result<(), BitVecError> {
        let bv = BitVec::try_from(42i8)?;
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.to_u64().unwrap(), 42);

        let bv = BitVec::try_from(0i8)?;
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.to_u64().unwrap(), 0);

        let bv = BitVec::try_from(-42i8)?;
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.to_u64().unwrap() & 0xFF, 214u64); // -42i8 as u8 = 214, mask to 8 bits

        Ok(())
    }

    #[test]
    fn test_from_i16() -> Result<(), BitVecError> {
        let bv = BitVec::try_from(4242i16)?;
        assert_eq!(bv.len(), 16);
        assert_eq!(bv.to_u64().unwrap(), 4242);

        let bv = BitVec::try_from(-4242i16)?;
        assert_eq!(bv.len(), 16);
        assert_eq!(bv.to_u64().unwrap() & 0xFFFF, 61294u64); // -4242i16 as u16 = 61294, mask to 16 bits

        Ok(())
    }

    #[test]
    fn test_from_i32() -> Result<(), BitVecError> {
        let bv = BitVec::try_from(424242i32)?;
        assert_eq!(bv.len(), 32);
        assert_eq!(bv.to_u64().unwrap(), 424242);

        let bv = BitVec::try_from(-424242i32)?;
        assert_eq!(bv.len(), 32);
        assert_eq!(bv.to_u64().unwrap() & 0xFFFFFFFF, 4294543054u64); // -424242i32 as u32 = 4294543054, mask to 32 bits

        Ok(())
    }

    #[test]
    fn test_from_i64() -> Result<(), BitVecError> {
        let bv = BitVec::try_from(42424242i64)?;
        assert_eq!(bv.len(), 64);
        assert_eq!(bv.to_u64().unwrap(), 42424242);

        let bv = BitVec::try_from(-42424242i64)?;
        assert_eq!(bv.len(), 64);
        assert_eq!(bv.to_u64().unwrap(), (-42424242i64) as u64);

        Ok(())
    }

    #[test]
    fn test_from_i128() -> Result<(), BitVecError> {
        let bv = BitVec::try_from(4242424242424242i128)?;
        assert_eq!(bv.len(), 128);
        assert!(bv.to_u64().is_none()); // Too large for u64
        assert_eq!(
            bv.to_biguint(),
            num_bigint::BigUint::try_from(4242424242424242u128)?
        );

        let bv = BitVec::try_from(-4242424242424242i128)?;
        assert_eq!(bv.len(), 128);
        assert!(bv.to_u64().is_none());
        assert_eq!(
            bv.to_biguint(),
            num_bigint::BigUint::try_from((-4242424242424242i128) as u128)?
        );

        Ok(())
    }
}
