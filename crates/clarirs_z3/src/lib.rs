mod convert;

use clarirs_core::prelude::*;

pub struct Z3Model<'c, 'z> {
    ctx: &'c Context<'c>,
    z3_ctx: &'z z3::Context,
    model: z3::Model<'z>,
}

impl<'c> Model<'c> for Z3Model<'c, '_> {
    fn eval_bool(&self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        convert::convert_bool_from_z3(
            self.ctx,
            &self
                .model
                .get_const_interp(&convert::convert_bool_to_z3(self.z3_ctx, expr)?)
                .ok_or(ClarirsError::AstNotInModel)?,
        )
    }

    fn eval_bitvec(&self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        convert::convert_bv_from_z3(
            self.ctx,
            &self
                .model
                .get_const_interp(&convert::convert_bv_to_z3(self.z3_ctx, expr)?)
                .ok_or(ClarirsError::AstNotInModel)?,
        )
    }

    fn eval_float(&self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        convert::convert_float_from_z3(
            self.ctx,
            &self
                .model
                .get_const_interp(&convert::convert_float_to_z3(self.z3_ctx, expr)?)
                .ok_or(ClarirsError::AstNotInModel)?,
        )
    }

    fn eval_string(&self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        convert::convert_string_from_z3(
            self.ctx,
            &self
                .model
                .get_const_interp(&convert::convert_string_to_z3(self.z3_ctx, expr)?)
                .ok_or(ClarirsError::AstNotInModel)?,
        )
    }
}

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
    type Model = Z3Model<'c, 'z>;

    fn add(&mut self, constraint: &BoolAst<'c>) -> Result<(), ClarirsError> {
        let z3_constraint = convert::convert_bool_to_z3(self.solver.get_context(), constraint)?;
        self.solver.assert(&z3_constraint);
        Ok(())
    }

    fn model(&mut self) -> Result<Self::Model, ClarirsError> {
        if self.solver.check() != z3::SatResult::Sat {
            return Err(ClarirsError::Unsat);
        }

        let model = self.solver.get_model().unwrap();

        Ok(Z3Model {
            ctx: self.ctx,
            z3_ctx: self.solver.get_context(),
            model,
        })
    }
}
