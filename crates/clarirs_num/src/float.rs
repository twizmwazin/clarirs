use serde::{Deserialize, Serialize};

use super::BitVec;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FSort {
    exponent: u32,
    mantissa: u32,
}

impl FSort {
    pub fn new(exponent: u32, mantissa: u32) -> Self {
        Self { exponent, mantissa }
    }

    pub fn exponent(&self) -> u32 {
        self.exponent
    }

    pub fn mantissa(&self) -> u32 {
        self.mantissa
    }

    pub fn size(&self) -> u32 {
        self.exponent + self.mantissa + 1
    }

    pub fn f32() -> Self {
        Self::new(8, 23)
    }

    pub fn f64() -> Self {
        Self::new(11, 52)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub enum FPRM {
    #[default]
    NearestTiesToEven,
    TowardPositive,
    TowardNegative,
    TowardZero,
    NearestTiesToAway,
}

/// A dynamic floating-point number representation. We follow the IEEE 754
/// standard wherever possible.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Float {
    sign: bool,
    exponent: BitVec,
    mantissa: BitVec,
}

impl Float {
    pub fn new(sign: bool, exponent: BitVec, mantissa: BitVec) -> Self {
        Self {
            sign,
            exponent,
            mantissa,
        }
    }

    pub fn sign(&self) -> bool {
        self.sign
    }

    pub fn exponent(&self) -> &BitVec {
        &self.exponent
    }

    pub fn mantissa(&self) -> &BitVec {
        &self.mantissa
    }

    pub fn fsort(&self) -> FSort {
        FSort::new(self.exponent.len() as u32, self.mantissa.len() as u32)
    }

    pub fn to_fsort(&self, fsort: FSort, rm: FPRM) -> Self {
        // TODO: This implementation only currently works for the same fsort

        let exponent = match fsort.exponent().cmp(&(self.exponent.len() as u32)) {
            std::cmp::Ordering::Less => todo!(),
            std::cmp::Ordering::Equal => self.exponent.clone(),
            std::cmp::Ordering::Greater => todo!(),
        };

        let mantissa = match fsort.mantissa().cmp(&(self.mantissa.len() as u32)) {
            std::cmp::Ordering::Less => todo!(),
            std::cmp::Ordering::Equal => self.mantissa.clone(),
            std::cmp::Ordering::Greater => todo!(),
        };

        Self::new(self.sign, exponent, mantissa)
    }
}

impl From<f32> for Float {
    fn from(value: f32) -> Self {
        let (sign, exponent, mantissa) = decompose_f32(value);
        Self {
            sign: sign == 1,
            exponent: BitVec::from_prim_with_size(exponent, 8),
            mantissa: BitVec::from_prim_with_size(mantissa, 23),
        }
    }
}

impl From<f64> for Float {
    fn from(value: f64) -> Self {
        let (sign, exponent, mantissa) = decompose_f64(value);
        Self {
            sign: sign == 1,
            exponent: BitVec::from_prim_with_size(exponent, 11),
            mantissa: BitVec::from_prim_with_size(mantissa, 52),
        }
    }
}

pub fn decompose_f32(value: f32) -> (u8, u8, u32) {
    let bits: u32 = value.to_bits();
    let sign: u8 = (bits >> 31) as u8;
    let exponent: u8 = ((bits >> 23) & 0xFF) as u8;
    let mantissa: u32 = bits & 0x7FFFFF;

    (sign, exponent, mantissa)
}

pub fn recompose_f32(sign: u8, exponent: u8, mantissa: u32) -> f32 {
    let sign_bit: u32 = (sign as u32) << 31;
    let exponent_bits: u32 = ((exponent as u32) & 0xFF) << 23;
    let mantissa_bits: u32 = mantissa & 0x7FFFFF;
    let bits: u32 = sign_bit | exponent_bits | mantissa_bits;

    f32::from_bits(bits)
}

pub fn decompose_f64(value: f64) -> (u8, u16, u64) {
    let bits: u64 = value.to_bits();
    let sign: u8 = (bits >> 63) as u8;
    let exponent: u16 = ((bits >> 52) & 0x7FF) as u16;
    let mantissa: u64 = bits & 0xFFFFFFFFFFFFF;

    (sign, exponent, mantissa)
}

pub fn recompose_f64(sign: u8, exponent: u16, mantissa: u64) -> f64 {
    let sign_bit: u64 = (sign as u64) << 63;
    let exponent_bits: u64 = ((exponent as u64) & 0x7FF) << 52;
    let mantissa_bits: u64 = mantissa & 0xFFFFFFFFFFFFF;
    let bits: u64 = sign_bit | exponent_bits | mantissa_bits;

    f64::from_bits(bits)
}

pub fn decompose_f64_big_endian(value: f64) -> (u8, u16, u64) {
    let bits: u64 = value.to_bits().to_be();
    let sign: u8 = (bits >> 63) as u8;
    let exponent: u16 = ((bits >> 52) & 0x7FF) as u16;
    let mantissa: u64 = bits & 0xFFFFFFFFFFFFF;

    (sign, exponent, mantissa)
}

pub fn recompose_f64_big_endian(sign: u8, exponent: u16, mantissa: u64) -> f64 {
    let sign_bit: u64 = (sign as u64) << 63;
    let exponent_bits: u64 = ((exponent as u64) & 0x7FF) << 52;
    let mantissa_bits: u64 = mantissa & 0xFFFFFFFFFFFFF;
    let bits: u64 = sign_bit | exponent_bits | mantissa_bits;

    f64::from_bits(bits.to_be())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_float_decomposition() {
        // Test cases for decompose and recompose functions
        let values = [
            0.0,
            -0.0,
            1.0,
            -1.0,
            42.0,
            -42.0,
            1.5,
            -1.5,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::NAN,
        ];

        for &value in &values {
            let (sign, exponent, mantissa) = decompose_f64(value);
            let recomposed = recompose_f64(sign, exponent, mantissa);

            // Check for NaN explicitly as NaN != NaN
            if value.is_nan() {
                assert!(recomposed.is_nan());
            } else {
                assert_eq!(value, recomposed);
            }

            let (sign_be, exponent_be, mantissa_be) = decompose_f64_big_endian(value);
            let recomposed_be = recompose_f64_big_endian(sign_be, exponent_be, mantissa_be);

            // Check for NaN explicitly as NaN != NaN
            if value.is_nan() {
                assert!(recomposed_be.is_nan());
            } else {
                assert_eq!(value, recomposed_be);
            }
        }
    }
}
