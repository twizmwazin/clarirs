use clarirs_core::prelude::*;

/// A solver that uses Value Set Analysis (VSA) for symbolic computation
#[derive(Clone)]
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
    fn constraints(&self) -> Result<Vec<BoolAst<'c>>, ClarirsError> {
        Ok(vec![])
    }

    fn add(&mut self, _: &BoolAst<'c>) -> Result<(), ClarirsError> {
        Err(ClarirsError::UnsupportedOperation(
            "Adding constraints is not supported in VSASolver".to_string(),
        ))
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        Ok(true)
    }

    fn eval_bool(&mut self, _expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        todo!("Implement eval_bool for VSASolver")
    }

    fn eval_bitvec(&mut self, _expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        todo!("Implement eval_bitvec for VSASolver")
    }

    fn eval_float(&mut self, _expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        todo!("Implement eval_float for VSASolver")
    }

    fn eval_string(&mut self, _expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        todo!("Implement eval_string for VSASolver")
    }

    fn is_true(&mut self, _expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        todo!("Implement is_true for VSASolver")
    }

    fn is_false(&mut self, _expr: &BoolAst<'c>) -> Result<bool, ClarirsError> {
        todo!("Implement is_false for VSASolver")
    }

    fn min(&mut self, _expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        todo!("Implement min for VSASolver")
    }

    fn max(&mut self, _expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        todo!("Implement max for VSASolver")
    }
}
