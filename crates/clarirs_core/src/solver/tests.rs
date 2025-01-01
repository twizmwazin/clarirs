use crate::prelude::*;
use crate::solver::concrete::ConcreteModel;

#[test]
fn test_min() -> Result<(), ClarirsError> {
    let ctx = Context::new();
    let model = ConcreteModel;

    let a = ctx.bvv_prim(5u64)?;
    let b = ctx.bvv_prim(3u64)?;

    let add_expr = ctx.add(&a, &b)?;
    let sub_expr = ctx.sub(&a, &b)?;
    let mul_expr = ctx.mul(&a, &b)?;

    let min_add = model.min(&add_expr)?;
    let min_sub = model.min(&sub_expr)?;
    let min_mul = model.min(&mul_expr)?;

    assert_eq!(min_add, ctx.bvv_prim(8u64)?);
    assert_eq!(min_sub, ctx.bvv_prim(2u64)?);
    assert_eq!(min_mul, ctx.bvv_prim(15u64)?);

    Ok(())
}

#[test]
fn test_max() -> Result<(), ClarirsError> {
    let ctx = Context::new();
    let model = ConcreteModel;

    let a = ctx.bvv_prim(5u64)?;
    let b = ctx.bvv_prim(3u64)?;

    let add_expr = ctx.add(&a, &b)?;
    let sub_expr = ctx.sub(&a, &b)?;
    let mul_expr = ctx.mul(&a, &b)?;

    let max_add = model.max(&add_expr)?;
    let max_sub = model.max(&sub_expr)?;
    let max_mul = model.max(&mul_expr)?;

    assert_eq!(max_add, ctx.bvv_prim(8u64)?);
    assert_eq!(max_sub, ctx.bvv_prim(2u64)?);
    assert_eq!(max_mul, ctx.bvv_prim(15u64)?);

    Ok(())
}
