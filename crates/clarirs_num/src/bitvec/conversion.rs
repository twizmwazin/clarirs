use num_bigint::BigUint;
use smallvec::SmallVec;

use super::{BitVec, BitVecError};

impl From<i8> for BitVec {
    fn from(value: i8) -> Self {
        BitVec::new(SmallVec::from_slice(&[value as u64]), 8)
    }
}

impl From<u8> for BitVec {
    fn from(value: u8) -> Self {
        BitVec::new(SmallVec::from_slice(&[value as u64]), 8)
    }
}

impl From<i16> for BitVec {
    fn from(value: i16) -> Self {
        BitVec::new(SmallVec::from_slice(&[value as u64]), 16)
    }
}

impl From<u16> for BitVec {
    fn from(value: u16) -> Self {
        BitVec::new(SmallVec::from_slice(&[value as u64]), 16)
    }
}

impl From<i32> for BitVec {
    fn from(value: i32) -> Self {
        BitVec::new(SmallVec::from_slice(&[value as u64]), 32)
    }
}

impl From<u32> for BitVec {
    fn from(value: u32) -> Self {
        BitVec::new(SmallVec::from_slice(&[value as u64]), 32)
    }
}

impl From<i64> for BitVec {
    fn from(value: i64) -> Self {
        BitVec::new(
            SmallVec::from_slice(&[unsafe { std::mem::transmute::<i64, u64>(value) }]),
            64,
        )
    }
}

impl From<u64> for BitVec {
    fn from(value: u64) -> Self {
        BitVec::new(SmallVec::from_slice(&[value]), 64)
    }
}

impl From<i128> for BitVec {
    fn from(value: i128) -> Self {
        BitVec::new(
            SmallVec::from_slice(&[value as u64, (value >> 64) as u64]),
            128,
        )
    }
}

impl From<u128> for BitVec {
    fn from(value: u128) -> Self {
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

impl From<&BitVec> for BigUint {
    fn from(bv: &BitVec) -> Self {
        BigUint::from_bytes_be(
            bv.words
                .iter()
                .flat_map(|w| w.to_be_bytes())
                .collect::<Vec<u8>>()
                .as_slice(),
        )
    }
}
