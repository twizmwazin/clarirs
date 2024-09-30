use anyhow::Result;

use crate::prelude::*;

pub struct ConcreteModel;

impl<'c> Model<'c> for ConcreteModel {
    fn batch_eval<I>(&self, exprs: I, _: u32) -> Result<Vec<AstRef<'c>>, ClarirsError>
    where
        I: IntoIterator<Item = AstRef<'c>>,
    {
        exprs
            .into_iter()
            .map(|e| {
                if e.symbolic() {
                    Err(ClarirsError::UnsupportedOperation)
                } else {
                    Ok(e.simplify()?)
                }
            })
            .collect::<Result<Vec<AstRef<'c>>, ClarirsError>>()
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

impl<'c, 's> Solver<'c, 's> for ConcreteSolver<'c>
where
    'c: 's,
{
    type Model = ConcreteModel;

    fn add(&'s mut self, _: &AstRef<'c>) -> Result<(), ClarirsError> {
        Err(ClarirsError::UnsupportedOperation)
    }

    fn model(&'s mut self) -> Result<Self::Model, ClarirsError> {
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
        solver.eval(&context.true_()?)?;
        solver.eval(&context.false_()?)?;
        assert!(solver.eval(&context.bools("test")?).is_err());

        // BV tests
        assert!(
            solver.eval(&context.add(&context.bvv_prim(1u8)?, &context.bvv_prim(1u8)?)?)?
                == context.bvv_prim(2u8)?
        );
        assert!(solver.eval(&context.bvs("test", 8)?).is_err());

        Ok(())
    }
}
