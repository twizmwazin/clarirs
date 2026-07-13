use clarirs_core::prelude::*;
use num_traits::Signed;

use crate::{reduce::Reduce, strided_interval::ComparisonResult};

/// A solver that uses Value Set Analysis (VSA) for symbolic computation
#[derive(Clone, Debug)]
pub struct VSASolver<'c> {
    ctx: &'c Context<'c>,
}

impl<'c> VSASolver<'c> {
    /// Create a new VSA solver
    pub fn new(ctx: &'c Context<'c>) -> Self {
        Self { ctx }
    }
}

impl<'c> HasContext<'c> for VSASolver<'c> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c> Solver<'c> for VSASolver<'c> {
    fn add(&mut self, _: &AstRef<'c>) -> Result<(), ClarirsError> {
        Ok(())
    }

    fn clear(&mut self) -> Result<(), ClarirsError> {
        Ok(())
    }

    fn constraints(&self) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        Ok(vec![])
    }

    fn simplify(&mut self) -> Result<(), ClarirsError> {
        Ok(())
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        Ok(true)
    }

    fn eval_n(&mut self, expr: &AstRef<'c>, n: u32) -> Result<Vec<AstRef<'c>>, ClarirsError> {
        match expr.ast_type() {
            AstType::Bool => expr
                .simplify()?
                .reduce()?
                .into_bool()
                .and_then(|comp_result| match comp_result {
                    ComparisonResult::True => Ok(vec![self.context().boolv(true)?]),
                    ComparisonResult::False => Ok(vec![self.context().boolv(false)?]),
                    ComparisonResult::Maybe => match n {
                        0 => Ok(vec![]),
                        1 => Ok(vec![self.context().boolv(true)?]),
                        _ => Ok(vec![
                            self.context().boolv(true)?,
                            self.context().boolv(false)?,
                        ]),
                    },
                }),
            AstType::BitVec(_) => expr.simplify()?.reduce()?.into_bv().and_then(|si| {
                if si.is_empty() {
                    return Ok(vec![]);
                }
                si.eval(n)
                    .into_iter()
                    .map(|bv| self.context().bvv(BitVec::from((bv, expr.size()))))
                    .collect()
            }),
            AstType::Float(_) | AstType::String => Err(ClarirsError::UnsupportedOperation(
                "Only boolean and bitvector evaluation is supported in VSASolver".to_string(),
            )),
        }
    }

    fn is_true(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        Ok(matches!(
            expr.simplify()?.reduce()?.into_bool()?,
            ComparisonResult::True
        ))
    }

    fn is_false(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        Ok(matches!(
            expr.simplify()?.reduce()?.into_bool()?,
            ComparisonResult::False
        ))
    }

    fn has_true(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        Ok(matches!(
            expr.simplify()?.reduce()?.into_bool()?,
            ComparisonResult::True | ComparisonResult::Maybe
        ))
    }

    fn has_false(&mut self, expr: &AstRef<'c>) -> Result<bool, ClarirsError> {
        Ok(matches!(
            expr.simplify()?.reduce()?.into_bool()?,
            ComparisonResult::False | ComparisonResult::Maybe
        ))
    }

    fn min_unsigned(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        expr.simplify()?.reduce()?.into_bv().and_then(|si| {
            let (min_bound, _) = si.get_unsigned_bounds();
            expr.context().bvv(BitVec::from((min_bound, expr.size())))
        })
    }

    fn max_unsigned(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        expr.simplify()?.reduce()?.into_bv().and_then(|si| {
            let (_, max_bound) = si.get_unsigned_bounds();
            expr.context().bvv(BitVec::from((max_bound, expr.size())))
        })
    }

    fn min_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        expr.simplify()?.reduce()?.into_bv().and_then(|si| {
            let (min_bound, _) = si.get_signed_bounds();
            // Convert BigInt back to unsigned representation for two's complement
            let unsigned_min = if min_bound.is_negative() {
                let modulus = num_bigint::BigUint::from(1u32) << expr.size();
                let abs_val = (-min_bound.clone()).to_biguint().unwrap();
                &modulus - &abs_val
            } else {
                min_bound.to_biguint().unwrap()
            };
            expr.context()
                .bvv(BitVec::from((unsigned_min, expr.size())))
        })
    }

    fn max_signed(&mut self, expr: &AstRef<'c>) -> Result<AstRef<'c>, ClarirsError> {
        expr.simplify()?.reduce()?.into_bv().and_then(|si| {
            let (_, max_bound) = si.get_signed_bounds();
            // Convert BigInt back to unsigned representation for two's complement
            let unsigned_max = if max_bound.is_negative() {
                let modulus = num_bigint::BigUint::from(1u32) << expr.size();
                let abs_val = (-max_bound.clone()).to_biguint().unwrap();
                &modulus - &abs_val
            } else {
                max_bound.to_biguint().unwrap()
            };
            expr.context()
                .bvv(BitVec::from((unsigned_max, expr.size())))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    fn bv<'c>(ctx: &'c Context<'c>, value: u64, bits: u32) -> AstRef<'c> {
        ctx.bvv(BitVec::from((value, bits))).unwrap()
    }

    fn si<'c>(ctx: &'c Context<'c>, bits: u32, stride: u32, lb: u32, ub: u32) -> AstRef<'c> {
        ctx.si(
            bits,
            BigUint::from(stride),
            BigUint::from(lb),
            BigUint::from(ub),
        )
        .unwrap()
    }

    #[test]
    fn test_constraint_management_is_noop() {
        let ctx = Context::new();
        let mut solver = VSASolver::new(&ctx);

        // VSA is constraint-free: everything is a no-op and always sat
        let c = ctx.boolv(true).unwrap();
        solver.add(&c).unwrap();
        assert!(solver.constraints().unwrap().is_empty());
        solver.simplify().unwrap();
        solver.clear().unwrap();
        assert!(solver.satisfiable().unwrap());
    }

    #[test]
    fn test_eval_bool_concrete() {
        let ctx = Context::new();
        let mut solver = VSASolver::new(&ctx);

        let t = ctx.boolv(true).unwrap();
        let f = ctx.boolv(false).unwrap();
        assert_eq!(solver.eval(&t).unwrap(), t);
        assert_eq!(solver.eval(&f).unwrap(), f);
    }

    #[test]
    fn test_eval_n_bool_symbolic() {
        let ctx = Context::new();
        let mut solver = VSASolver::new(&ctx);
        let s = ctx.bools("b").unwrap();
        let t = ctx.boolv(true).unwrap();
        let f = ctx.boolv(false).unwrap();

        assert_eq!(solver.eval_n(&s, 0).unwrap(), vec![]);
        assert_eq!(solver.eval_n(&s, 1).unwrap(), vec![t.clone()]);
        assert_eq!(solver.eval_n(&s, 2).unwrap(), vec![t.clone(), f.clone()]);
        // More than two requested still yields only the two possible values
        assert_eq!(solver.eval_n(&s, 5).unwrap(), vec![t, f]);
    }

    #[test]
    fn test_eval_bv_concrete() {
        let ctx = Context::new();
        let mut solver = VSASolver::new(&ctx);
        let x = bv(&ctx, 42, 32);
        assert_eq!(solver.eval(&x).unwrap(), x);
    }

    #[test]
    fn test_eval_n_bv_strided() {
        let ctx = Context::new();
        let mut solver = VSASolver::new(&ctx);
        // 2[1, 5] contains exactly {1, 3, 5}
        let x = si(&ctx, 8, 2, 1, 5);
        assert_eq!(
            solver.eval_n(&x, 10).unwrap(),
            vec![bv(&ctx, 1, 8), bv(&ctx, 3, 8), bv(&ctx, 5, 8)]
        );
        // The limit truncates the result
        assert_eq!(
            solver.eval_n(&x, 2).unwrap(),
            vec![bv(&ctx, 1, 8), bv(&ctx, 3, 8)]
        );
    }

    #[test]
    fn test_eval_n_empty_si() {
        let ctx = Context::new();
        let mut solver = VSASolver::new(&ctx);
        let e = ctx.esi(8).unwrap();
        assert_eq!(solver.eval_n(&e, 10).unwrap(), vec![]);
    }

    #[test]
    fn test_eval_float_unsupported() {
        let ctx = Context::new();
        let mut solver = VSASolver::new(&ctx);
        let f = ctx.fpv_from_f64(1.0).unwrap();
        assert!(solver.eval_n(&f, 1).is_err());
    }

    #[test]
    fn test_is_true_is_false() {
        let ctx = Context::new();
        let mut solver = VSASolver::new(&ctx);

        let t = ctx.boolv(true).unwrap();
        let f = ctx.boolv(false).unwrap();
        assert!(solver.is_true(&t).unwrap());
        assert!(!solver.is_true(&f).unwrap());
        assert!(solver.is_false(&f).unwrap());
        assert!(!solver.is_false(&t).unwrap());

        // x == x simplifies to true, x != x to false
        let x = ctx.bvs("x", 32).unwrap();
        assert!(solver.is_true(&ctx.eq_(&x, &x).unwrap()).unwrap());
        assert!(solver.is_false(&ctx.neq(&x, &x).unwrap()).unwrap());
    }

    #[test]
    fn test_has_true_has_false_maybe() {
        let ctx = Context::new();
        let mut solver = VSASolver::new(&ctx);

        // x < 5 with unconstrained x is Maybe: could be true or false
        let x = ctx.bvs("x", 32).unwrap();
        let cmp = ctx.ult(&x, bv(&ctx, 5, 32)).unwrap();
        assert!(!solver.is_true(&cmp).unwrap());
        assert!(!solver.is_false(&cmp).unwrap());
        assert!(solver.has_true(&cmp).unwrap());
        assert!(solver.has_false(&cmp).unwrap());

        // Concrete truths also "have" their value
        let t = ctx.boolv(true).unwrap();
        assert!(solver.has_true(&t).unwrap());
        assert!(!solver.has_false(&t).unwrap());
    }

    #[test]
    fn test_min_max_unsigned() {
        let ctx = Context::new();
        let mut solver = VSASolver::new(&ctx);

        let x = si(&ctx, 32, 1, 10, 20);
        assert_eq!(solver.min_unsigned(&x).unwrap(), bv(&ctx, 10, 32));
        assert_eq!(solver.max_unsigned(&x).unwrap(), bv(&ctx, 20, 32));

        // A constant is its own min and max
        let c = bv(&ctx, 42, 32);
        assert_eq!(solver.min_unsigned(&c).unwrap(), c);
        assert_eq!(solver.max_unsigned(&c).unwrap(), c);
    }

    #[test]
    fn test_min_max_unsigned_wrapping() {
        let ctx = Context::new();
        let mut solver = VSASolver::new(&ctx);

        // 1[250, 5] wraps around 0, so unsigned bounds widen to [0, 255]
        let x = si(&ctx, 8, 1, 250, 5);
        assert_eq!(solver.min_unsigned(&x).unwrap(), bv(&ctx, 0, 8));
        assert_eq!(solver.max_unsigned(&x).unwrap(), bv(&ctx, 255, 8));
    }

    #[test]
    fn test_min_max_signed_negative_range() {
        let ctx = Context::new();
        let mut solver = VSASolver::new(&ctx);

        // 1[246, 250] is [-10, -6] signed
        let x = si(&ctx, 8, 1, 246, 250);
        assert_eq!(solver.min_signed(&x).unwrap(), bv(&ctx, 246, 8));
        assert_eq!(solver.max_signed(&x).unwrap(), bv(&ctx, 250, 8));
    }

    #[test]
    fn test_min_max_signed_wrapping_range() {
        let ctx = Context::new();
        let mut solver = VSASolver::new(&ctx);

        // 1[250, 5] is the contiguous signed range [-6, 5]
        let x = si(&ctx, 8, 1, 250, 5);
        assert_eq!(solver.min_signed(&x).unwrap(), bv(&ctx, 250, 8));
        assert_eq!(solver.max_signed(&x).unwrap(), bv(&ctx, 5, 8));
    }

    #[test]
    fn test_min_max_signed_positive() {
        let ctx = Context::new();
        let mut solver = VSASolver::new(&ctx);
        let c = bv(&ctx, 5, 8);
        assert_eq!(solver.min_signed(&c).unwrap(), c);
        assert_eq!(solver.max_signed(&c).unwrap(), c);
    }
}
