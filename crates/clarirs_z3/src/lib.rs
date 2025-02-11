mod astext;
mod convert;

use clarirs_core::prelude::*;
use z3::ast::Ast;

thread_local! {
    static Z3_CONTEXT: z3::Context = z3::Context::new(&z3::Config::new());
}

#[derive(Clone)]
pub struct Z3Solver<'c> {
    ctx: &'c Context<'c>,
    assertions: Vec<BoolAst<'c>>,
}

impl<'c> Z3Solver<'c> {
    pub fn new(ctx: &'c Context<'c>) -> Self {
        Self { ctx, assertions: vec![] }
    }
}

impl<'c> HasContext<'c> for Z3Solver<'c> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c> Solver<'c> for Z3Solver<'c> {
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError> {
        self.assertions.push(constraint.clone());
        Ok(())
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        Z3_CONTEXT.with(|z3_ctx| {
            let z3_solver = z3::Solver::new(z3_ctx);
            for assertion in &self.assertions {
                z3_solver.assert(&convert::convert_bool_to_z3(z3_ctx, assertion)?);
            }

            Ok(z3_solver.check() == z3::SatResult::Sat)
        })
    }

    fn eval_bool(&mut self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|z3_ctx| {
            let z3_solver = z3::Solver::new(z3_ctx);
            for assertion in &self.assertions {
                z3_solver.assert(&convert::convert_bool_to_z3(z3_ctx, assertion)?);
            }

            if z3_solver.check() != z3::SatResult::Sat {
                return Err(ClarirsError::Unsat);
            }

            convert::convert_bool_from_z3(
                self.ctx,
                &z3_solver
                    .get_model()
                    .ok_or(ClarirsError::Unsat)?
                    .get_const_interp(&convert::convert_bool_to_z3(z3_ctx, expr)?)
                    .ok_or(ClarirsError::AstNotInModel)?,
            )
        })
    }

    fn eval_bitvec(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|z3_ctx| {
            let z3_solver = z3::Solver::new(z3_ctx);
            for assertion in &self.assertions {
                z3_solver.assert(&convert::convert_bool_to_z3(z3_ctx, assertion)?);
            }

            if z3_solver.check() != z3::SatResult::Sat {
                return Err(ClarirsError::Unsat);
            }

            convert::convert_bv_from_z3(
                self.ctx,
                &z3_solver
                    .get_model()
                    .ok_or(ClarirsError::Unsat)?
                    .get_const_interp(&convert::convert_bv_to_z3(z3_ctx, expr)?)
                    .ok_or(ClarirsError::AstNotInModel)?,
            )
        })
    }

    fn eval_float(&mut self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|z3_ctx| {
            let z3_solver = z3::Solver::new(z3_ctx);
            for assertion in &self.assertions {
                z3_solver.assert(&convert::convert_bool_to_z3(z3_ctx, assertion)?);
            }

            if z3_solver.check() != z3::SatResult::Sat {
                return Err(ClarirsError::Unsat);
            }

            convert::convert_float_from_z3(
                self.ctx,
                &z3_solver
                    .get_model()
                    .ok_or(ClarirsError::Unsat)?
                    .get_const_interp(&convert::convert_float_to_z3(z3_ctx, expr)?)
                    .ok_or(ClarirsError::AstNotInModel)?,
            )
        })
    }

    fn eval_string(&mut self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|z3_ctx| {
            let z3_solver = z3::Solver::new(z3_ctx);
            for assertion in &self.assertions {
                z3_solver.assert(&convert::convert_bool_to_z3(z3_ctx, assertion)?);
            }

            if z3_solver.check() != z3::SatResult::Sat {
                return Err(ClarirsError::Unsat);
            }

            convert::convert_string_from_z3(
                self.ctx,
                &z3_solver
                    .get_model()
                    .ok_or(ClarirsError::Unsat)?
                    .get_const_interp(&convert::convert_string_to_z3(z3_ctx, expr)?)
                    .ok_or(ClarirsError::AstNotInModel)?,
            )
        })
    }

    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        Z3_CONTEXT.with(|z3_ctx| {
            Ok(convert::convert_bool_to_z3(z3_ctx, expr)?.simplify()
                == z3::ast::Bool::from_bool(z3_ctx, true))
        })
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        Z3_CONTEXT.with(|z3_ctx| {
            Ok(convert::convert_bool_to_z3(z3_ctx, expr)?.simplify()
                == z3::ast::Bool::from_bool(z3_ctx, false))
        })
    }

    fn min(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|z3_ctx| {
            let optimize = z3::Optimize::new(z3_ctx);
            for assertion in &self.assertions {
                optimize.assert(&convert::convert_bool_to_z3(z3_ctx, assertion)?);
            }
            let z3_expr = convert::convert_bv_to_z3(z3_ctx, expr)?;
            optimize.minimize(&z3_expr);

            let model = optimize.get_model().ok_or(ClarirsError::Unsat)?;
            convert::convert_bv_from_z3(
                self.ctx,
                &model
                    .get_const_interp(&z3_expr)
                    .ok_or(ClarirsError::AstNotInModel)?,
            )
        })
    }

    fn max(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        Z3_CONTEXT.with(|z3_ctx| {
            let optimize = z3::Optimize::new(z3_ctx);
            for assertion in &self.assertions {
                optimize.assert(&convert::convert_bool_to_z3(z3_ctx, assertion)?);
            }
            let z3_expr = convert::convert_bv_to_z3(z3_ctx, expr)?;
            optimize.maximize(&z3_expr);

            let model = optimize.get_model().ok_or(ClarirsError::Unsat)?;
            convert::convert_bv_from_z3(
                self.ctx,
                &model
                    .get_const_interp(&z3_expr)
                    .ok_or(ClarirsError::AstNotInModel)?,
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_solver() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        let mut solver = Z3Solver::new(&ctx);

        let x = ctx.bools("x")?;
        let y = ctx.bools("y")?;

        solver.add(&ctx.not(&ctx.eq_(&x, &y)?)?).unwrap();

        let x_val = solver.eval_bool(&x).unwrap();
        let y_val = solver.eval_bool(&y).unwrap();

        assert_ne!(x_val, y_val);

        Ok(())
    }

    #[test]
    fn test_solver_unsat() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        let mut solver = Z3Solver::new(&ctx);

        let x = ctx.bools("x")?;
        let y = ctx.bools("y")?;

        solver.add(&ctx.eq_(&x, &y)?)?;
        solver.add(&ctx.neq(&x, &y)?)?;

        assert!(!solver.satisfiable()?);

        Ok(())
    }

    #[test]
    fn test_solver_bool() -> Result<(), ClarirsError> {
        let ctx = Context::new();

        let mut solver = Z3Solver::new(&ctx);

        let x = ctx.bools("x")?;
        let y = ctx.bools("y")?;

        solver.add(&ctx.not(&ctx.eq_(&x, &y)?)?).unwrap();
        solver.add(&ctx.eq_(&x, &ctx.true_()?)?).unwrap();

        let x_val = solver.eval_bool(&x).unwrap();
        let y_val = solver.eval_bool(&y).unwrap();

        assert_ne!(x_val, y_val);
        assert!(x_val.is_true());
        assert!(y_val.is_false());

        Ok(())
    }
}
