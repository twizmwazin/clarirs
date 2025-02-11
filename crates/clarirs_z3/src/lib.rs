mod astext;
mod convert;

use clarirs_core::prelude::*;

#[derive(Clone)]
pub struct Z3Solver<'c, 'z> {
    ctx: &'c Context<'c>,
    solver: z3::Solver<'z>,
}

impl<'c, 'z> Z3Solver<'c, 'z> {
    pub fn new(ctx: &'c Context<'c>, z3_ctx: &'z z3::Context) -> Self {
        Self {
            ctx,
            solver: z3::Solver::new(z3_ctx),
        }
    }
}

impl<'c> HasContext<'c> for Z3Solver<'c, '_> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c, 'z> Solver<'c> for Z3Solver<'c, 'z> {
    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError> {
        let z3_constraint = convert::convert_bool_to_z3(self.solver.get_context(), constraint)?;
        self.solver.assert(&z3_constraint);
        Ok(())
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        Ok(self.solver.check() == z3::SatResult::Sat)
    }

    fn eval_bool(&mut self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        if self.solver.check() != z3::SatResult::Sat {
            return Err(ClarirsError::Unsat);
        }
        convert::convert_bool_from_z3(
            self.ctx,
            &self
                .solver
                .get_model()
                .ok_or(ClarirsError::Unsat)?
                .get_const_interp(&convert::convert_bool_to_z3(
                    self.solver.get_context(),
                    expr,
                )?)
                .ok_or(ClarirsError::AstNotInModel)?,
        )
    }

    fn eval_bitvec(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if self.solver.check() != z3::SatResult::Sat {
            return Err(ClarirsError::Unsat);
        }
        convert::convert_bv_from_z3(
            self.ctx,
            &self
                .solver
                .get_model()
                .ok_or(ClarirsError::Unsat)?
                .get_const_interp(&convert::convert_bv_to_z3(
                    self.solver.get_context(),
                    expr,
                )?)
                .ok_or(ClarirsError::AstNotInModel)?,
        )
    }

    fn eval_float(&mut self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        if self.solver.check() != z3::SatResult::Sat {
            return Err(ClarirsError::Unsat);
        }
        convert::convert_float_from_z3(
            self.ctx,
            &self
                .solver
                .get_model()
                .ok_or(ClarirsError::Unsat)?
                .get_const_interp(&convert::convert_float_to_z3(
                    self.solver.get_context(),
                    expr,
                )?)
                .ok_or(ClarirsError::AstNotInModel)?,
        )
    }

    fn eval_string(&mut self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        if self.solver.check() != z3::SatResult::Sat {
            return Err(ClarirsError::Unsat);
        }
        convert::convert_string_from_z3(
            self.ctx,
            &self
                .solver
                .get_model()
                .ok_or(ClarirsError::Unsat)?
                .get_const_interp(&convert::convert_string_to_z3(
                    self.solver.get_context(),
                    expr,
                )?)
                .ok_or(ClarirsError::AstNotInModel)?,
        )
    }

    fn is_true(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let z3_expr = convert::convert_bool_to_z3(self.solver.get_context(), expr)?;
        Ok(self.solver.check_assumptions(&[z3_expr]) == z3::SatResult::Sat)
    }

    fn is_false(&mut self, expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        let z3_expr = convert::convert_bool_to_z3(self.solver.get_context(), expr)?;
        Ok(self.solver.check_assumptions(&[z3_expr]) == z3::SatResult::Unsat)
    }

    fn min(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let optimize = z3::Optimize::new(self.solver.get_context());
        for assertion in self.solver.get_assertions() {
            optimize.assert(&assertion);
        }
        let z3_expr = convert::convert_bv_to_z3(self.solver.get_context(), expr)?;
        optimize.minimize(&z3_expr);

        let model = optimize.get_model().ok_or(ClarirsError::Unsat)?;
        convert::convert_bv_from_z3
            (
                self.ctx,
                &model
                    .get_const_interp(&z3_expr)
                    .ok_or(ClarirsError::AstNotInModel)?,
            )

    }

    fn max(&mut self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        let optimize = z3::Optimize::new(self.solver.get_context());
        for assertion in self.solver.get_assertions() {
            optimize.assert(&assertion);
        }
        let z3_expr = convert::convert_bv_to_z3(self.solver.get_context(), expr)?;
        optimize.maximize(&z3_expr);

        let model = optimize.get_model().ok_or(ClarirsError::Unsat)?;
        convert::convert_bv_from_z3
            (
                self.ctx,
                &model
                    .get_const_interp(&z3_expr)
                    .ok_or(ClarirsError::AstNotInModel)?,
            )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn setup<'c>() -> (Context<'c>, z3::Context) {
        let ctx = Context::new();
        let z3_cfg = z3::Config::new();
        let z3_ctx = z3::Context::new(&z3_cfg);

        (ctx, z3_ctx)
    }

    #[test]
    fn test_solver() -> Result<(), ClarirsError> {
        let (ctx, z3_ctx) = setup();

        let mut solver = Z3Solver::new(&ctx, &z3_ctx);

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
        let (ctx, z3_ctx) = setup();

        let mut solver = Z3Solver::new(&ctx, &z3_ctx);

        let x = ctx.bools("x")?;
        let y = ctx.bools("y")?;

        solver.add(&ctx.eq_(&x, &y)?)?;
        solver.add(&ctx.neq(&x, &y)?)?;

        assert!(!solver.satisfiable()?);

        Ok(())
    }

    #[test]
    fn test_solver_bool() -> Result<(), ClarirsError> {
        let (ctx, z3_ctx) = setup();

        let mut solver = Z3Solver::new(&ctx, &z3_ctx);

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
