use clarirs_core::prelude::*;
use num_bigint::BigUint;
use num_traits::One;

use crate::{reduce::Reduce, strided_interval::ComparisonResult};

pub trait Cardinality {
    fn cardinality(&self) -> Result<BigUint, ClarirsError>;
}

impl Cardinality for AstRef<'_> {
    fn cardinality(&self) -> Result<BigUint, ClarirsError> {
        match self.ast_type() {
            AstType::BitVec(_) => Ok(self.reduce()?.into_bv()?.cardinality()),
            AstType::Bool => match self.reduce()?.into_bool()? {
                ComparisonResult::True | ComparisonResult::False => Ok(BigUint::one()),
                ComparisonResult::Maybe => Ok(BigUint::from(2u32)),
            },
            _ => Err(ClarirsError::UnsupportedOperation(
                "Cardinality is not supported for this type".to_string(),
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cardinality_bv_constant() {
        let ctx = Context::new();
        let x = ctx.bvv(BitVec::from((42u64, 32))).unwrap();
        assert_eq!(x.cardinality().unwrap(), BigUint::one());
    }

    #[test]
    fn test_cardinality_bv_symbol_is_full_range() {
        let ctx = Context::new();
        let x = ctx.bvs("x", 32).unwrap();
        assert_eq!(x.cardinality().unwrap(), BigUint::one() << 32);

        let y = ctx.bvs("y", 8).unwrap();
        assert_eq!(y.cardinality().unwrap(), BigUint::from(256u32));
    }

    #[test]
    fn test_cardinality_strided_interval() {
        let ctx = Context::new();
        // 2[10, 20] contains {10, 12, 14, 16, 18, 20}
        let x = ctx
            .si(
                32,
                BigUint::from(2u32),
                BigUint::from(10u32),
                BigUint::from(20u32),
            )
            .unwrap();
        assert_eq!(x.cardinality().unwrap(), BigUint::from(6u32));
    }

    #[test]
    fn test_cardinality_empty_si() {
        let ctx = Context::new();
        let e = ctx.esi(32).unwrap();
        assert_eq!(e.cardinality().unwrap(), BigUint::from(0u32));
    }

    #[test]
    fn test_cardinality_bool() {
        let ctx = Context::new();
        assert_eq!(
            ctx.boolv(true).unwrap().cardinality().unwrap(),
            BigUint::one()
        );
        assert_eq!(
            ctx.boolv(false).unwrap().cardinality().unwrap(),
            BigUint::one()
        );
        // An unconstrained boolean has two possible values
        assert_eq!(
            ctx.bools("b").unwrap().cardinality().unwrap(),
            BigUint::from(2u32)
        );
    }

    #[test]
    fn test_cardinality_bool_expression() {
        let ctx = Context::new();
        let five = ctx.bvv(BitVec::from((5u64, 32))).unwrap();
        let x = ctx.bvs("x", 32).unwrap();

        // A definitely-true comparison has one value
        let eq = ctx.eq_(&five, &five).unwrap();
        assert_eq!(eq.cardinality().unwrap(), BigUint::one());

        // A maybe comparison has two
        let cmp = ctx.ult(&x, &five).unwrap();
        assert_eq!(cmp.cardinality().unwrap(), BigUint::from(2u32));
    }

    #[test]
    fn test_cardinality_unsupported_types() {
        let ctx = Context::new();
        assert!(ctx.fpv_from_f64(1.0).unwrap().cardinality().is_err());
        assert!(ctx.stringv("hello").unwrap().cardinality().is_err());
    }
}
