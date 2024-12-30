use anyhow::Result;

use crate::prelude::*;

pub struct ConcreteModel;

impl<'c> Model<'c> for ConcreteModel {
    fn eval_bool(&self, expr: &BoolAst<'c>) -> Result<BoolAst<'c>, ClarirsError> {
        if expr.symbolic() {
            return Err(ClarirsError::UnsupportedOperation);
        }
        expr.simplify()
    }

    fn eval_bitvec(&self, expr: &BitVecAst<'c>) -> Result<BitVecAst<'c>, ClarirsError> {
        if expr.symbolic() {
            return Err(ClarirsError::UnsupportedOperation);
        }
        expr.simplify()
    }

    fn eval_float(&self, expr: &FloatAst<'c>) -> Result<FloatAst<'c>, ClarirsError> {
        if expr.symbolic() {
            return Err(ClarirsError::UnsupportedOperation);
        }
        expr.simplify()
    }

    fn eval_string(&self, expr: &StringAst<'c>) -> Result<StringAst<'c>, ClarirsError> {
        if expr.symbolic() {
            return Err(ClarirsError::UnsupportedOperation);
        }
        expr.simplify()
    }
}

/// A concrete solver. This solver is used to evaluate expressions in a concrete
/// context. It does not support adding constraints. It is a glorified
/// simplifier.
#[derive(Clone)]
pub struct ConcreteSolver<'c> {
    ctx: &'c Context<'c>,
}

impl<'c> HasContext<'c> for ConcreteSolver<'c> {
    fn context(&self) -> &'c Context<'c> {
        self.ctx
    }
}

impl<'c> ConcreteSolver<'c> {
    pub fn new(ctx: &'c Context<'c>) -> Result<Self, ClarirsError> {
        Ok(Self { ctx })
    }
}

impl<'c> Solver<'c> for ConcreteSolver<'c> {
    type Model = ConcreteModel;

    fn add(&mut self, _: &BoolAst<'c>) -> Result<(), ClarirsError> {
        Err(ClarirsError::UnsupportedOperation)
    }

    fn model(&mut self) -> Result<Self::Model, ClarirsError> {
        Ok(ConcreteModel)
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::AstFactory;

    use super::*;

    #[test]
    fn test_concrete_solver() -> Result<()> {
        let context = Context::new();
        let mut solver = ConcreteSolver::new(&context)?;

        // Bool tests
        solver.eval_bool(&context.true_()?)?;
        solver.eval_bool(&context.false_()?)?;
        assert!(solver.eval_bool(&context.bools("test")?).is_err());

        // BV tests
        assert!(
            solver.eval_bitvec(&context.add(&context.bvv_prim(1u8)?, &context.bvv_prim(1u8)?)?)?
                == context.bvv_prim(2u8)?
        );
        assert!(solver.eval_bitvec(&context.bvs("test", 8)?).is_err());

        Ok(())
    }
}
