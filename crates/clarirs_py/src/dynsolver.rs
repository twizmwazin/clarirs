use clarirs_core::prelude::*;
use clarirs_z3::Z3Solver;

#[derive(Clone)]
pub(crate) enum DynSolver {
    ConcreteSolver(ConcreteSolver<'static>),
    Z3Solver(Z3Solver<'static>),
}

impl HasContext<'static> for DynSolver {
    fn context(&self) -> &'static Context<'static> {
        match self {
            DynSolver::ConcreteSolver(solver) => solver.context(),
            DynSolver::Z3Solver(solver) => solver.context(),
        }
    }
}

impl Solver<'static> for DynSolver {
    fn constraints(&self) -> Result<Vec<BoolAst<'static>>, ClarirsError> {
        match self {
            DynSolver::ConcreteSolver(solver) => solver.constraints(),
            DynSolver::Z3Solver(solver) => solver.constraints(),
        }
    }

    fn add(&mut self, constraint: &BoolAst<'static>) -> Result<(), ClarirsError> {
        match self {
            DynSolver::ConcreteSolver(solver) => solver.add(constraint),
            DynSolver::Z3Solver(solver) => solver.add(constraint),
        }
    }

    fn satisfiable(&mut self) -> Result<bool, ClarirsError> {
        match self {
            DynSolver::ConcreteSolver(solver) => solver.satisfiable(),
            DynSolver::Z3Solver(solver) => solver.satisfiable(),
        }
    }

    fn eval_bool(&mut self, expr: &BoolAst<'static>) -> Result<BoolAst<'static>, ClarirsError> {
        match self {
            DynSolver::ConcreteSolver(solver) => solver.eval_bool(expr),
            DynSolver::Z3Solver(solver) => solver.eval_bool(expr),
        }
    }

    fn eval_bitvec(
        &mut self,
        expr: &BitVecAst<'static>,
    ) -> Result<BitVecAst<'static>, ClarirsError> {
        match self {
            DynSolver::ConcreteSolver(solver) => solver.eval_bitvec(expr),
            DynSolver::Z3Solver(solver) => solver.eval_bitvec(expr),
        }
    }

    fn eval_float(&mut self, expr: &FloatAst<'static>) -> Result<FloatAst<'static>, ClarirsError> {
        match self {
            DynSolver::ConcreteSolver(solver) => solver.eval_float(expr),
            DynSolver::Z3Solver(solver) => solver.eval_float(expr),
        }
    }

    fn eval_string(
        &mut self,
        expr: &StringAst<'static>,
    ) -> Result<StringAst<'static>, ClarirsError> {
        match self {
            DynSolver::ConcreteSolver(solver) => solver.eval_string(expr),
            DynSolver::Z3Solver(solver) => solver.eval_string(expr),
        }
    }

    fn is_true(&mut self, expr: &BoolAst<'static>) -> Result<bool, ClarirsError> {
        match self {
            DynSolver::ConcreteSolver(solver) => solver.is_true(expr),
            DynSolver::Z3Solver(solver) => solver.is_true(expr),
        }
    }

    fn is_false(&mut self, expr: &BoolAst<'static>) -> Result<bool, ClarirsError> {
        match self {
            DynSolver::ConcreteSolver(solver) => solver.is_false(expr),
            DynSolver::Z3Solver(solver) => solver.is_false(expr),
        }
    }

    fn min(&mut self, expr: &BitVecAst<'static>) -> Result<BitVecAst<'static>, ClarirsError> {
        match self {
            DynSolver::ConcreteSolver(solver) => solver.min(expr),
            DynSolver::Z3Solver(solver) => solver.min(expr),
        }
    }

    fn max(&mut self, expr: &BitVecAst<'static>) -> Result<BitVecAst<'static>, ClarirsError> {
        match self {
            DynSolver::ConcreteSolver(solver) => solver.max(expr),
            DynSolver::Z3Solver(solver) => solver.max(expr),
        }
    }
}
