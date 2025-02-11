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

impl<'c> Solver<'c> for Z3Solver<'c, '_> {
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
                .get_const_interp(&convert::convert_bv_to_z3(self.solver.get_context(), expr)?)
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
        convert::convert_bv_from_z3(
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
        convert::convert_bv_from_z3(
            self.ctx,
            &model
                .get_const_interp(&z3_expr)
                .ok_or(ClarirsError::AstNotInModel)?,
        )
    }
}
