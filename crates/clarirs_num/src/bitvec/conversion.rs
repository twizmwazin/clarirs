use num_bigint::{BigInt, BigUint};
use num_traits::Num;
use smallvec::SmallVec;

use super::{BitVec, BitVecError};

macro_rules! impl_from_unsigned {
    ($($ty:ty => $bits:expr),+ $(,)?) => {
        $(impl From<$ty> for BitVec {
            fn from(value: $ty) -> BitVec {
                Self::from_biguint(&BigUint::from(value), $bits)
            }
        })+
    };
}

macro_rules! impl_from_signed {
    ($($ty:ty => $bits:expr),+ $(,)?) => {
        $(impl From<$ty> for BitVec {
            fn from(value: $ty) -> BitVec {
                Self::from_bigint(&BigInt::from(value), $bits)
            }
        })+
    };
}

impl_from_unsigned!(u8 => 8, u16 => 16, u32 => 32, u64 => 64, u128 => 128);
impl_from_signed!(i8 => 8, i16 => 16, i32 => 32, i64 => 64, i128 => 128);

/// Builds a `BitVec` of an explicit `length` from a primitive value, truncating
/// to that width. This is the arbitrary-width primitive constructor (the fixed
/// `From<uN>`/`From<iN>` impls cover the type-width cases). Implemented over
/// concrete primitive types rather than a blanket `T: Into<u64>` so it doesn't
/// collide with `TryFrom<(&str, u32)>` through the std `TryFrom` blanket impl.
macro_rules! impl_from_prim_with_size {
    ($($ty:ty),+ $(,)?) => {
        $(impl From<($ty, u32)> for BitVec {
            fn from((value, length): ($ty, u32)) -> BitVec {
                let value_u64 = u64::from(value);
                let truncated = if length < 64 {
                    value_u64 & ((1u64 << length) - 1)
                } else {
                    value_u64
                };
                let mut words = SmallVec::new();
                words.push(truncated);
                BitVec::new(words, length)
            }
        })+
    };
}

impl_from_prim_with_size!(u8, u16, u32, u64);

/// Parses a base-10 string into a `BitVec` of the given width.
impl TryFrom<(&str, u32)> for BitVec {
    type Error = BitVecError;

    fn try_from((s, length): (&str, u32)) -> Result<BitVec, BitVecError> {
        let value = BigUint::from_str_radix(s, 10).map_err(|_| BitVecError::ConversionError)?;
        Ok(BitVec::from_biguint(&value, length))
    }
}

impl From<BitVec> for BigUint {
    fn from(bv: BitVec) -> Self {
        bv.to_biguint()
    }
}

impl From<&BitVec> for BigUint {
    fn from(bv: &BitVec) -> Self {
        bv.to_biguint()
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use num_traits::Zero;

    #[test]
    fn test_to_biguint() {
        use num_bigint::BigUint;
        use num_traits::One;

        // Test conversion of zero
        let bv = BitVec::zero(64);
        assert_eq!(bv.to_biguint(), BigUint::zero());

        // Test various positive values
        let bv = BitVec::from(42u64);
        assert_eq!(bv.to_biguint(), BigUint::from(42u64));

        // Test different widths
        let bv = BitVec::from(0xFFu8);
        assert_eq!(bv.to_biguint(), BigUint::from(0xFFu64));

        let bv = BitVec::from(0xFFFFu16);
        assert_eq!(bv.to_biguint(), BigUint::from(0xFFFFu64));

        // Test maximum value for width
        let bv = BitVec::from(u32::MAX);
        assert_eq!(bv.to_biguint(), BigUint::from(u32::MAX));

        // Test odd-sized vectors (e.g., 17 bits)
        let value = BigUint::from(0x1FFFFu64); // 17 bits set
        let bv = BitVec::from_biguint(&value, 17);
        assert_eq!(bv.to_biguint(), value);

        // Test single-bit vector
        let bv = BitVec::from((1u8, 1));
        assert_eq!(bv.to_biguint(), BigUint::one());

        // Test zero-width vector
        let bv = BitVec::zero(0);
        assert_eq!(bv.to_biguint(), BigUint::zero());

        // Test 72-bit vector
        let value = (BigUint::one() << 72u32) - BigUint::one(); // 2^72 - 1
        let bv = BitVec::from_biguint(&value, 72);
        assert_eq!(bv.to_biguint(), value);
    }

    #[test]
    fn test_from_biguint() {
        use num_bigint::BigUint;
        use num_traits::One;

        // Test conversion from zero
        let bv = BitVec::from_biguint(&BigUint::zero(), 64);
        assert_eq!(bv.to_u64().unwrap(), 0);

        // Test various positive values
        let value = BigUint::from(42u64);
        let bv = BitVec::from_biguint(&value, 64);
        assert_eq!(bv.to_u64().unwrap(), 42);

        // Test value truncation
        let value = BigUint::from(0xFFu64);
        let bv = BitVec::from_biguint(&value, 4);
        assert_eq!(bv.to_u64().unwrap(), 0xF); // 0xFF truncated to 4 bits = 0xF

        // Test explicit truncation function
        let value = BigUint::from(0xFFu64);
        let bv = BitVec::from_biguint(&value, 4);
        assert_eq!(bv.to_u64().unwrap() & 0xF, 0xF); // Only compare the lowest 4 bits

        // Test different widths
        let value = BigUint::from(0xFFu64);
        let bv = BitVec::from_biguint(&value, 8);
        assert_eq!(bv.to_u64().unwrap(), 0xFF);

        // Test odd-sized vectors
        let value = BigUint::from(0x1Fu64); // 5 bits
        let bv = BitVec::from_biguint(&value, 5);
        assert_eq!(bv.to_u64().unwrap(), 0x1F);

        // Test single-bit vector
        let bv = BitVec::from_biguint(&BigUint::one(), 1);
        assert_eq!(bv.to_u64().unwrap(), 1);

        // Test zero-width vector
        let bv = BitVec::from_biguint(&BigUint::zero(), 0);
        assert_eq!(bv.len(), 0);
    }

    #[test]
    fn test_to_u64() {
        // Test conversion of zero
        let bv = BitVec::zero(64);
        assert_eq!(bv.to_u64().unwrap(), 0);

        // Test conversion of various values
        let bv = BitVec::from(42u64);
        assert_eq!(bv.to_u64().unwrap(), 42);

        // Test width > 64 (should error)
        let bv = BitVec::zero(65);
        assert!(bv.to_u64().is_none());

        // Test different widths
        let bv = BitVec::from(0xFFu8);
        assert_eq!(bv.to_u64().unwrap(), 0xFF);

        let bv = BitVec::from(0xFFFFu16);
        assert_eq!(bv.to_u64().unwrap(), 0xFFFF);

        // Test maximum value for width
        let bv = BitVec::from(u32::MAX);
        assert_eq!(bv.to_u64().unwrap(), u32::MAX as u64);

        // Test odd-sized vectors
        let bv = BitVec::from((0x1Fu8, 5)); // 5 bits
        assert_eq!(bv.to_u64().unwrap(), 0x1F);

        // Test single-bit vector
        let bv = BitVec::from((1u8, 1));
        assert_eq!(bv.to_u64().unwrap(), 1);
    }

    #[test]
    fn test_to_usize() {
        // Test conversion of zero
        let bv = BitVec::zero(usize::BITS);
        assert_eq!(bv.to_usize().unwrap(), 0);

        // Test conversion of various values
        let bv = BitVec::from(42u64);
        assert_eq!(bv.to_usize().unwrap(), 42);

        // Test width > usize::BITS (should error)
        let bv = BitVec::zero(usize::BITS + 1);
        assert!(bv.to_usize().is_none());

        // Test different widths
        let bv = BitVec::from(0xFFu8);
        assert_eq!(bv.to_usize().unwrap(), 0xFF);

        let bv = BitVec::from(0xFFFFu16);
        assert_eq!(bv.to_usize().unwrap(), 0xFFFF);

        // Test maximum value for width
        let max_32bit = BitVec::from(u32::MAX);
        if usize::BITS >= 32 {
            assert_eq!(max_32bit.to_usize().unwrap(), u32::MAX as usize);
        } else {
            assert!(max_32bit.to_usize().is_none());
        }

        // Test odd-sized vectors
        let bv = BitVec::from((0x1Fu8, 5)); // 5 bits
        assert_eq!(bv.to_usize().unwrap(), 0x1F);

        // Test single-bit vector
        let bv = BitVec::from((1u8, 1));
        assert_eq!(bv.to_usize().unwrap(), 1);
    }

    #[test]
    fn test_from_u8() {
        let bv = BitVec::from(42u8);
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.to_u64().unwrap(), 42);

        let bv = BitVec::from(0u8);
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.to_u64().unwrap(), 0);

        let bv = BitVec::from(255u8);
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.to_u64().unwrap(), 255);
    }

    #[test]
    fn test_from_u16() {
        let bv = BitVec::from(4242u16);
        assert_eq!(bv.len(), 16);
        assert_eq!(bv.to_u64().unwrap(), 4242);

        let bv = BitVec::from(0u16);
        assert_eq!(bv.len(), 16);
        assert_eq!(bv.to_u64().unwrap(), 0);

        let bv = BitVec::from(u16::MAX);
        assert_eq!(bv.len(), 16);
        assert_eq!(bv.to_u64().unwrap(), u16::MAX as u64);
    }

    #[test]
    fn test_from_u32() {
        let bv = BitVec::from(424242u32);
        assert_eq!(bv.len(), 32);
        assert_eq!(bv.to_u64().unwrap(), 424242);

        let bv = BitVec::from(0u32);
        assert_eq!(bv.len(), 32);
        assert_eq!(bv.to_u64().unwrap(), 0);

        let bv = BitVec::from(u32::MAX);
        assert_eq!(bv.len(), 32);
        assert_eq!(bv.to_u64().unwrap(), u32::MAX as u64);
    }

    #[test]
    fn test_from_u64() {
        let bv = BitVec::from(42424242u64);
        assert_eq!(bv.len(), 64);
        assert_eq!(bv.to_u64().unwrap(), 42424242);

        let bv = BitVec::from(0u64);
        assert_eq!(bv.len(), 64);
        assert_eq!(bv.to_u64().unwrap(), 0);

        let bv = BitVec::from(u64::MAX);
        assert_eq!(bv.len(), 64);
        assert_eq!(bv.to_u64().unwrap(), u64::MAX);
    }

    #[test]
    fn test_from_u128() {
        let bv = BitVec::from(4242424242424242u128);
        assert_eq!(bv.len(), 128);
        assert!(bv.to_u64().is_none()); // Too large for u64
        assert_eq!(
            bv.to_biguint(),
            num_bigint::BigUint::from(4242424242424242u128)
        );

        let bv = BitVec::from(0u128);
        assert_eq!(bv.len(), 128);
        assert!(bv.to_u64().is_none()); // Even 0 should return None for 128-bit vectors

        let bv = BitVec::from(u128::MAX);
        assert_eq!(bv.len(), 128);
        assert!(bv.to_u64().is_none());
        assert_eq!(bv.to_biguint(), num_bigint::BigUint::from(u128::MAX));
    }

    #[test]
    fn test_from_i8() {
        let bv = BitVec::from(42i8);
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.to_u64().unwrap(), 42);

        let bv = BitVec::from(0i8);
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.to_u64().unwrap(), 0);

        let bv = BitVec::from(-42i8);
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.to_u64().unwrap() & 0xFF, 214u64); // -42i8 as u8 = 214, mask to 8 bits

        let bv = BitVec::from(-1i8);
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.to_u64().unwrap(), 255);
    }

    #[test]
    fn test_from_i16() {
        let bv = BitVec::from(4242i16);
        assert_eq!(bv.len(), 16);
        assert_eq!(bv.to_u64().unwrap(), 4242);

        let bv = BitVec::from(-4242i16);
        assert_eq!(bv.len(), 16);
        assert_eq!(bv.to_u64().unwrap() & 0xFFFF, 61294u64); // -4242i16 as u16 = 61294, mask to 16 bits
    }

    #[test]
    fn test_from_i32() {
        let bv = BitVec::from(424242i32);
        assert_eq!(bv.len(), 32);
        assert_eq!(bv.to_u64().unwrap(), 424242);

        let bv = BitVec::from(-424242i32);
        assert_eq!(bv.len(), 32);
        assert_eq!(bv.to_u64().unwrap() & 0xFFFFFFFF, 4294543054u64); // -424242i32 as u32 = 4294543054, mask to 32 bits
    }

    #[test]
    fn test_from_i64() {
        let bv = BitVec::from(42424242i64);
        assert_eq!(bv.len(), 64);
        assert_eq!(bv.to_u64().unwrap(), 42424242);

        let bv = BitVec::from(-42424242i64);
        assert_eq!(bv.len(), 64);
        assert_eq!(bv.to_u64().unwrap(), (-42424242i64) as u64);
    }

    #[test]
    fn test_from_i128() {
        let bv = BitVec::from(4242424242424242i128);
        assert_eq!(bv.len(), 128);
        assert!(bv.to_u64().is_none()); // Too large for u64
        assert_eq!(
            bv.to_biguint(),
            num_bigint::BigUint::from(4242424242424242u128)
        );

        let bv = BitVec::from(-4242424242424242i128);
        assert_eq!(bv.len(), 128);
        assert!(bv.to_u64().is_none());
        assert_eq!(
            bv.to_biguint(),
            num_bigint::BigUint::from((-4242424242424242i128) as u128)
        );
    }
}
