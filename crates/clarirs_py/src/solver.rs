use std::collections::HashSet;

use crate::{dynsolver::DynSolver, prelude::*};
use clarirs_core::ast::bitvec::BitVecOpExt;
use clarirs_vsa::VSASolver;
use clarirs_z3::Z3Solver;
use num_bigint::BigInt;
use pyo3::types::PyTuple;

#[pyclass(name = "Solver", module = "clarirs.solver", subclass)]
pub struct PySolver {
    inner: DynSolver,
}

#[pymethods]
impl PySolver {
    #[new]
    fn new() -> Result<PyClassInitializer<Self>, ClaripyError> {
        Ok(PyClassInitializer::from(PySolver {
            inner: DynSolver::Z3(Z3Solver::new(&GLOBAL_CONTEXT)),
        }))
    }

    fn blank_copy(&self) -> Result<PySolver, ClaripyError> {
        Ok(PySolver {
            inner: match &self.inner {
                DynSolver::Concrete(..) => {
                    DynSolver::Concrete(ConcreteSolver::new(&GLOBAL_CONTEXT))
                }
                DynSolver::Z3(..) => DynSolver::Z3(Z3Solver::new(&GLOBAL_CONTEXT)),
                DynSolver::Vsa(..) => DynSolver::Vsa(VSASolver::new(&GLOBAL_CONTEXT)),
            },
        })
    }

    #[getter]
    fn constraints<'py>(&self, py: Python<'py>) -> Result<Vec<Bound<'py, Bool>>, ClaripyError> {
        self.inner
            .constraints()?
            .iter()
            .map(|c| Bool::new(py, c))
            .collect::<Result<Vec<_>, _>>()
    }

    #[getter]
    fn variables(&self) -> Result<HashSet<String>, ClaripyError> {
        Ok(self.inner.variables()?)
    }

    fn branch<'py>(&self, py: Python<'py>) -> Result<Bound<'py, PySolver>, ClaripyError> {
        match &self.inner {
            DynSolver::Concrete(concrete_solver) => Ok(Bound::new(
                py,
                PySolver {
                    inner: DynSolver::Concrete(concrete_solver.clone()),
                },
            )?),
            DynSolver::Z3(z3_solver) => Ok(Bound::new(
                py,
                PySolver {
                    inner: DynSolver::Z3(z3_solver.clone()),
                },
            )?),
            DynSolver::Vsa(vsasolver) => Ok(Bound::new(
                py,
                PySolver {
                    inner: DynSolver::Vsa(vsasolver.clone()),
                },
            )?),
        }
    }

    #[pyo3(signature = (exprs))]
    fn add<'py>(
        &mut self,
        exprs: Bound<'py, PyAny>,
    ) -> Result<Vec<Bound<'py, Bool>>, ClaripyError> {
        // Handle both tuple of expressions and single expression
        let bool_exprs = if let Ok(tuple) = exprs.downcast::<PyTuple>() {
            // Convert tuple of expressions to Vec<Bound<Bool>>
            tuple
                .iter()
                .map(|expr| {
                    expr.downcast_into::<Bool>().map_err(|_| {
                        ClaripyError::TypeError("add: expression must be a boolean".to_string())
                    })
                })
                .collect::<Result<Vec<_>, _>>()?
        } else {
            // Handle single expression case
            vec![exprs.downcast_into::<Bool>().map_err(|_| {
                ClaripyError::TypeError("add: expression must be a boolean".to_string())
            })?]
        };

        // Add all expressions to the solver
        for expr in &bool_exprs {
            self.inner.add(&expr.get().inner)?;
        }

        Ok(bool_exprs)
    }

    #[pyo3(signature = (extra_constraints = None, exact = None))]
    fn satisfiable<'py>(
        &mut self,
        extra_constraints: Option<Vec<CoerceBool<'py>>>,
        exact: Option<Bound<'py, PyAny>>,
    ) -> Result<bool, ClaripyError> {
        let _ = exact; // TODO: Implement approximate solutions

        // If there are no extra constraints, use the original solver
        if extra_constraints.is_none() {
            return Ok(self.inner.satisfiable()?);
        }

        // Otherwise, clone the solver and add the constraints
        let mut solver = self.inner.clone();
        for constraint in extra_constraints.unwrap() {
            solver.add(&constraint.0.get().inner)?;
        }

        // Check satisfiability with the extra constraints
        Ok(solver.satisfiable()?)
    }

    #[pyo3(signature = (expr, n, extra_constraints = None, exact = None))]
    fn eval_to_ast<'py>(
        &mut self,
        py: Python<'py>,
        expr: Bound<'py, Base>,
        n: u32,
        extra_constraints: Option<Vec<CoerceBool<'py>>>,
        exact: Option<Bound<'py, PyAny>>,
    ) -> Result<Vec<Bound<'py, Base>>, ClaripyError> {
        let _ = exact; // TODO: Implement approximate solutions

        // Fork the solver for extra constraints
        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for constraint in extra_constraints {
                solver.add(&constraint.0.get().inner)?;
            }
        }

        // Get multiple solutions based on expression type
        if let Ok(bv_value) = expr.clone().into_any().downcast::<BV>() {
            // Use the new multi-solution trait method
            let solutions = solver.eval_bitvec_n(&bv_value.get().inner, n)?;
            let py_solutions = solutions
                .into_iter()
                .map(|sol| BV::new(py, &sol))
                .collect::<Result<Vec<_>, _>>()?;

            // Convert to Base type
            Ok(py_solutions
                .into_iter()
                .map(|sol| sol.into_any().downcast::<Base>().unwrap().clone())
                .collect())
        } else if let Ok(bool_value) = expr.clone().into_any().downcast::<Bool>() {
            // Use the new multi-solution trait method
            let solutions = solver.eval_bool_n(&bool_value.get().inner, n)?;
            let py_solutions = solutions
                .into_iter()
                .map(|sol| Bool::new(py, &sol))
                .collect::<Result<Vec<_>, _>>()?;

            // Convert to Base type
            Ok(py_solutions
                .into_iter()
                .map(|sol| sol.into_any().downcast::<Base>().unwrap().clone())
                .collect())
        } else if let Ok(fp_value) = expr.clone().into_any().downcast::<FP>() {
            // Use the new multi-solution trait method
            let solutions = solver.eval_float_n(&fp_value.get().inner, n)?;
            let py_solutions = solutions
                .into_iter()
                .map(|sol| FP::new(py, &sol))
                .collect::<Result<Vec<_>, _>>()?;

            // Convert to Base type
            Ok(py_solutions
                .into_iter()
                .map(|sol| sol.into_any().downcast::<Base>().unwrap().clone())
                .collect())
        } else if let Ok(string_value) = expr.clone().into_any().downcast::<PyAstString>() {
            // Use the new multi-solution trait method
            let solutions = solver.eval_string_n(&string_value.get().inner, n)?;
            let py_solutions = solutions
                .into_iter()
                .map(|sol| PyAstString::new(py, &sol))
                .collect::<Result<Vec<_>, _>>()?;

            // Convert to Base type
            Ok(py_solutions
                .into_iter()
                .map(|sol| sol.into_any().downcast::<Base>().unwrap().clone())
                .collect())
        } else {
            return Err(ClaripyError::TypeError("Unsupported type".to_string()));
        }
    }

    #[pyo3(signature = (expr, n, extra_constraints = None, exact = None))]
    fn eval<'py>(
        &mut self,
        py: Python<'py>,
        expr: Bound<'py, Base>,
        n: u32,
        extra_constraints: Option<Vec<CoerceBool<'py>>>,
        exact: Option<Bound<'py, PyAny>>,
    ) -> PyResult<Vec<Bound<'py, PyAny>>> {
        match self.eval_to_ast(py, expr, n, extra_constraints, exact) {
            Ok(results) => results
                .into_iter()
                .filter_map(|r| {
                    if let Ok(bv_value) = r.clone().into_any().downcast::<BV>() {
                        if let BitVecOp::BVV(bv) = bv_value.get().inner.op() {
                            Some(bv.to_biguint().into_bound_py_any(py))
                        } else {
                            None
                        }
                    } else if let Ok(bool_value) = r.clone().into_any().downcast::<Bool>() {
                        if let BooleanOp::BoolV(b) = bool_value.get().inner.op() {
                            Some(b.into_bound_py_any(py))
                        } else {
                            None
                        }
                    } else if let Ok(fp_value) = r.clone().into_any().downcast::<FP>() {
                        if let FloatOp::FPV(fp) = fp_value.get().inner.op() {
                            fp.to_f64().map(|f| f.into_bound_py_any(py))
                        } else {
                            None
                        }
                    } else if let Ok(string_value) = r.clone().into_any().downcast::<PyAstString>()
                    {
                        if let StringOp::StringV(s) = string_value.get().inner.op() {
                            Some(s.into_bound_py_any(py))
                        } else {
                            None
                        }
                    } else {
                        Some(Err(ClaripyError::UnsupportedOperation(
                            "eval: Unsupported type".to_string(),
                        )
                        .into()))
                    }
                })
                .collect::<Result<Vec<Bound<PyAny>>, pyo3::PyErr>>(),
            Err(e) => {
                if e.to_string().contains("UNSAT") {
                    Ok(vec![]) // Return empty list on UNSAT
                } else {
                    Err(e.into())
                }
            }
        }
    }

    #[pyo3(signature = (exprs, n, extra_constraints = None, exact = None))]
    fn batch_eval<'py>(
        &mut self,
        py: Python<'py>,
        exprs: Vec<Bound<'py, Base>>,
        n: u32,
        extra_constraints: Option<Vec<CoerceBool<'py>>>,
        exact: Option<Bound<'py, PyAny>>,
    ) -> PyResult<Vec<Vec<Bound<'py, PyAny>>>> {
        exprs
            .into_iter()
            .map(|expr| self.eval(py, expr, n, extra_constraints.clone(), exact.clone()))
            .collect::<Result<Vec<Vec<Bound<PyAny>>>, pyo3::PyErr>>()
    }

    #[pyo3(signature = (expr, value, extra_constraints = None, exact = None))]
    fn solution(
        &self,
        expr: Bound<Base>,
        value: Bound<PyAny>,
        extra_constraints: Option<Vec<Bound<Bool>>>,
        exact: Option<Bound<PyAny>>,
    ) -> Result<bool, ClaripyError> {
        _ = exact; // TODO: Implement approximate solutions

        // Fork the solver for extra constraints
        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for expr in extra_constraints {
                solver.add(&expr.get().inner)?;
            }
        }

        // Add the solution as a constraint, and check if it is satisfiable
        if let Ok(bool_ast) = expr.downcast::<Bool>() {
            if let Ok(value) = value.extract::<CoerceBool>() {
                Ok(solver.has_true(
                    &self
                        .inner
                        .context()
                        .eq_(&bool_ast.get().inner, &value.into())?,
                )?)
            } else {
                let value_type = value.get_type().name()?.extract::<String>()?;
                Err(ClaripyError::TypeError(format!(
                    "can't coerce a {} to a bool ast",
                    value_type
                )))
            }
        } else if let Ok(bv_ast) = expr.downcast::<BV>() {
            if let Ok(value) = value.extract::<CoerceBV>() {
                Ok(solver.has_true(&self.inner.context().eq_(
                    &bv_ast.get().inner,
                    &value.extract_like(bv_ast.py(), bv_ast.get())?.get().inner,
                )?)?)
            } else {
                let value_type = value.get_type().name()?.extract::<String>()?;
                Err(ClaripyError::TypeError(format!(
                    "can't coerce a {} to a bv ast",
                    value_type
                )))
            }
        } else if let Ok(fp_ast) = expr.downcast::<FP>() {
            if let Ok(value) = value.extract::<CoerceFP>() {
                Ok(solver.has_true(
                    &self
                        .inner
                        .context()
                        .eq_(&fp_ast.get().inner, &value.into())?,
                )?)
            } else {
                let value_type = value.get_type().name()?.extract::<String>()?;
                Err(ClaripyError::TypeError(format!(
                    "can't coerce a {} to a float ast",
                    value_type
                )))
            }
        } else if let Ok(string_ast) = expr.downcast::<PyAstString>() {
            if let Ok(value) = value.extract::<CoerceString>() {
                Ok(solver.has_true(
                    &self
                        .inner
                        .context()
                        .eq_(&string_ast.get().inner, &value.into())?,
                )?)
            } else {
                let value_type = value.get_type().name()?.extract::<String>()?;
                Err(ClaripyError::TypeError(format!(
                    "can't coerce a {} to a string ast",
                    value_type
                )))
            }
        } else {
            Err(ClaripyError::TypeError(
                "expression must be a boolean, bitvector, float, or string".to_string(),
            ))
        }
    }

    #[pyo3(signature = (expr, extra_constraints = None, exact = None))]
    fn is_true<'py>(
        &mut self,
        expr: Bound<'py, PyAny>,
        extra_constraints: Option<Vec<CoerceBool<'py>>>,
        exact: Option<Bound<'py, PyAny>>,
    ) -> Result<bool, ClaripyError> {
        _ = exact; // TODO: Implement approximate solutions

        // Check for Python primitive types first
        if let Ok(py_bool) = expr.extract::<bool>() {
            return Ok(py_bool);
        } else if let Ok(py_int) = expr.extract::<i64>() {
            return Ok(py_int != 0);
        }

        // Fork the solver for extra constraints
        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for constraint in extra_constraints {
                solver.add(&constraint.0.get().inner)?;
            }
        }

        // Handle different expression types
        if let Ok(bool_expr) = expr.downcast::<Bool>() {
            match bool_expr.get().inner.op() {
                BooleanOp::BoolV(b) => Ok(*b),
                _ => Ok(solver.is_true(&bool_expr.get().inner)?),
            }
        } else if let Ok(bv_expr) = expr.downcast::<BV>() {
            // For bitvectors, check if it's concrete and non-zero
            if let BitVecOp::BVV(bv) = bv_expr.get().inner.op() {
                Ok(!bv.is_zero())
            } else {
                // For symbolic BVs, check if it can be non-zero
                let zero = solver
                    .context()
                    .bvv_prim_with_size(0u64, bv_expr.get().inner.size())?;
                let eq_zero = solver.context().eq_(&bv_expr.get().inner, &zero)?;
                let is_zero = solver.is_true(&eq_zero)?;
                Ok(!is_zero)
            }
        } else {
            Err(ClaripyError::TypeError(
                "is_true: expression must be a boolean, integer, or bitvector".to_string(),
            ))
        }
    }

    #[pyo3(signature = (expr, extra_constraints = None, exact = None))]
    fn is_false<'py>(
        &mut self,
        expr: Bound<'py, PyAny>,
        extra_constraints: Option<Vec<CoerceBool<'py>>>,
        exact: Option<Bound<'py, PyAny>>,
    ) -> Result<bool, ClaripyError> {
        _ = exact; // TODO: Implement approximate solutions

        // Check for Python primitive types first
        if let Ok(py_bool) = expr.extract::<bool>() {
            return Ok(!py_bool);
        } else if let Ok(py_int) = expr.extract::<i64>() {
            return Ok(py_int == 0);
        }

        // Fork the solver for extra constraints
        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for constraint in extra_constraints {
                solver.add(&constraint.0.get().inner)?;
            }
        }

        // Handle different expression types
        if let Ok(bool_expr) = expr.downcast::<Bool>() {
            Ok(solver.is_false(&bool_expr.get().inner)?)
        } else if let Ok(bv_expr) = expr.downcast::<BV>() {
            // For bitvectors, check if it's concrete and zero
            if let BitVecOp::BVV(bv) = bv_expr.get().inner.op() {
                Ok(bv.is_zero())
            } else {
                // For symbolic BVs, check if it must be zero
                let zero = solver
                    .context()
                    .bvv_prim_with_size(0u64, bv_expr.get().inner.size())?;
                let eq_zero = solver.context().eq_(&bv_expr.get().inner, &zero)?;
                Ok(solver.is_true(&eq_zero)?)
            }
        } else {
            Err(ClaripyError::TypeError(
                "is_false: expression must be a boolean, integer, or bitvector".to_string(),
            ))
        }
    }

    #[pyo3(signature = (expr, extra_constraints = None, exact = None))]
    fn has_true<'py>(
        &mut self,
        expr: Bound<Bool>,
        extra_constraints: Option<Vec<CoerceBool<'py>>>,
        exact: Option<Bound<'py, PyAny>>,
    ) -> Result<bool, ClaripyError> {
        _ = exact; // TODO: Implement approximate solutions

        // Fork the solver for extra constraints
        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for constraint in extra_constraints {
                solver.add(&constraint.0.get().inner)?;
            }
        }

        Ok(solver.has_true(&expr.get().inner)?)
    }

    #[pyo3(signature = (expr, extra_constraints = None, exact = None))]
    fn has_false<'py>(
        &mut self,
        expr: Bound<Bool>,
        extra_constraints: Option<Vec<CoerceBool<'py>>>,
        exact: Option<Bound<'py, PyAny>>,
    ) -> Result<bool, ClaripyError> {
        _ = exact; // TODO: Implement approximate solutions

        // Fork the solver for extra constraints
        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for constraint in extra_constraints {
                solver.add(&constraint.0.get().inner)?;
            }
        }

        Ok(solver.has_false(&expr.get().inner)?)
    }

    #[pyo3(signature = (expr, extra_constraints = None, exact = None, signed = false))]
    fn min<'py>(
        &mut self,
        expr: Bound<'py, BV>,
        extra_constraints: Option<Vec<CoerceBool<'py>>>,
        exact: Option<Bound<'py, PyAny>>,
        signed: bool,
    ) -> Result<BigInt, ClaripyError> {
        let _ = exact; // TODO: Implement approximate solutions

        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for expr in extra_constraints {
                solver.add(&expr.0.get().inner)?;
            }
        }

        let result = if signed {
            solver.min_signed(&expr.get().inner)?
        } else {
            solver.min_unsigned(&expr.get().inner)?
        };

        if let BitVecOp::BVV(bv) = result.op() {
            Ok(BigInt::from(bv.to_biguint()))
        } else {
            Err(ClaripyError::TypeError(
                "max: expression must be a bitvector".to_string(),
            ))
        }
    }

    #[pyo3(signature = (expr, extra_constraints = None, exact = None, signed = false))]
    fn max<'py>(
        &mut self,
        expr: Bound<'py, BV>,
        extra_constraints: Option<Vec<CoerceBool<'py>>>,
        exact: Option<Bound<'py, PyAny>>,
        signed: bool,
    ) -> Result<BigInt, ClaripyError> {
        let _ = exact; // TODO: Implement approximate solutions

        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for expr in extra_constraints {
                solver.add(&expr.0.get().inner)?;
            }
        }

        let result = if signed {
            solver.max_signed(&expr.get().inner)?
        } else {
            solver.max_unsigned(&expr.get().inner)?
        };

        if let BitVecOp::BVV(bv) = result.op() {
            Ok(BigInt::from(bv.to_biguint()))
        } else {
            Err(ClaripyError::TypeError(
                "max: expression must be a bitvector".to_string(),
            ))
        }
    }
}

#[pyclass(extends = PySolver, name = "SolverConcrete", module = "clarirs.solver")]
pub struct PyConcreteSolver;

#[pymethods]
impl PyConcreteSolver {
    #[new]
    fn new() -> Result<PyClassInitializer<Self>, ClaripyError> {
        Ok(PyClassInitializer::from(PySolver {
            inner: DynSolver::Concrete(ConcreteSolver::new(&GLOBAL_CONTEXT)),
        })
        .add_subclass(Self {}))
    }
}

#[pyclass(extends = PySolver, name = "SolverZ3", module = "clarirs.solver")]
pub struct PyZ3Solver;

#[pymethods]
impl PyZ3Solver {
    #[new]
    fn new() -> Result<PyClassInitializer<Self>, ClaripyError> {
        Ok(PyClassInitializer::from(PySolver {
            inner: DynSolver::Z3(Z3Solver::new(&GLOBAL_CONTEXT)),
        })
        .add_subclass(Self {}))
    }
}

#[pyclass(extends = PySolver, name = "SolverVSA", module = "clarirs.solver")]
pub struct PyVSASolver;

#[pymethods]
impl PyVSASolver {
    #[new]
    fn new() -> Result<PyClassInitializer<Self>, ClaripyError> {
        Ok(PyClassInitializer::from(PySolver {
            inner: DynSolver::Vsa(VSASolver::new(&GLOBAL_CONTEXT)),
        })
        .add_subclass(Self {}))
    }

    fn has_true<'py>(slf: PyRefMut<'py, Self>, expr: Bound<'py, Bool>) -> PyResult<bool> {
        let mut py_solver: PyRefMut<'py, PySolver> = slf.into_super();
        match &mut py_solver.inner {
            DynSolver::Vsa(vsa_solver) => vsa_solver
                .has_true(&expr.get().inner)
                .map_err(|e| ClaripyError::from(e).into()),
            _ => {
                Err(ClaripyError::UnsupportedOperation("has_true not supported".to_string()).into())
            }
        }
    }

    fn has_false<'py>(slf: PyRefMut<'py, Self>, expr: Bound<'py, Bool>) -> PyResult<bool> {
        let mut py_solver: PyRefMut<'py, PySolver> = slf.into_super();
        match &mut py_solver.inner {
            DynSolver::Vsa(vsa_solver) => vsa_solver
                .has_false(&expr.get().inner)
                .map_err(|e| ClaripyError::from(e).into()),
            _ => Err(
                ClaripyError::UnsupportedOperation("has_false not supported".to_string()).into(),
            ),
        }
    }

    #[pyo3(signature = (expr, value, extra_constraints = None, exact = None))]
    fn solution<'py>(
        slf: PyRefMut<'py, Self>,
        expr: Bound<'py, Base>,
        value: Bound<'py, PyAny>,
        extra_constraints: Option<Vec<Bound<'py, Bool>>>,
        exact: Option<Bound<'py, PyAny>>,
    ) -> PyResult<bool> {
        let _ = exact; // TODO: Implement approximate solutions
        let _ = extra_constraints; // VSA solver doesn't support constraints

        // Get the parent solver
        let py_solver: PyRefMut<'py, PySolver> = slf.into_super();

        // Handle different expression types
        if let Ok(bv_ast) = expr.downcast::<BV>() {
            if let Ok(value) = value.extract::<CoerceBV>() {
                // Extract the value as a BigUint
                let value_bv = value.extract_like(bv_ast.py(), bv_ast.get())?;

                // Clone the solver to get a mutable version
                let mut solver = match &py_solver.inner {
                    DynSolver::Vsa(vsa_solver) => vsa_solver.clone(),
                    _ => {
                        return Err(ClaripyError::UnsupportedOperation(
                            "solution not supported".to_string(),
                        )
                        .into());
                    }
                };

                // Check if the value is concrete
                if let BitVecOp::BVV(_bv) = value_bv.get().inner.op() {
                    // Create an equality expression
                    let ctx = solver.context();
                    let eq_expr = match ctx.eq_(&bv_ast.get().inner, &value_bv.get().inner) {
                        Ok(expr) => expr,
                        Err(e) => return Err(ClaripyError::from(e).into()),
                    };

                    // Use the VSA solver to check if the equality can be true
                    match solver.has_true(&eq_expr) {
                        Ok(result) => Ok(result),
                        Err(e) => Err(ClaripyError::from(e).into()),
                    }
                } else {
                    // If the value is not concrete, we can't check
                    Ok(false)
                }
            } else {
                let value_type = value.get_type().name()?.extract::<String>()?;
                Err(
                    ClaripyError::TypeError(format!("can't coerce a {} to a bv ast", value_type))
                        .into(),
                )
            }
        } else {
            // For other types, fall back to the default implementation
            let super_method = py_solver.solution(expr, value, extra_constraints, exact)?;
            Ok(super_method)
        }
    }
}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<PySolver>()?;
    m.add_class::<PyConcreteSolver>()?;
    m.add_class::<PyZ3Solver>()?;
    m.add_class::<PyVSASolver>()?;

    Ok(())
}
