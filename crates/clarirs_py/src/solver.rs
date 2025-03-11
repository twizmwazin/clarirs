use std::collections::HashSet;

use crate::{dynsolver::DynSolver, prelude::*};
use clarirs_z3::Z3Solver;
use num_bigint::BigInt;
use pyo3::types::PyTuple;

#[pyclass(name = "Solver", module = "clarirs.solver", subclass)]
pub struct PySolver {
    inner: DynSolver,
}

#[pymethods]
impl PySolver {
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
        extra_constraints: Option<Vec<Bound<'py, Bool>>>,
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
            solver.add(&constraint.get().inner)?;
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
        extra_constraints: Option<Vec<Bound<'py, Bool>>>,
        exact: Option<Bound<'py, PyAny>>,
    ) -> Result<Vec<Bound<'py, Base>>, ClaripyError> {
        let _ = exact; // TODO: Implement approximate solutions

        // Create a vector to store solutions
        let mut results = Vec::new();

        // Fork the solver for extra constraints
        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for constraint in extra_constraints {
                solver.add(&constraint.get().inner)?;
            }
        }

        // Loop to find up to n solutions
        for _ in 0..n {
            // Check if solver is still satisfiable
            if !solver.satisfiable()? {
                break; // No more solutions
            }

            // Get a solution based on expression type
            let solution = if let Ok(bv_value) = expr.clone().into_any().downcast::<BV>() {
                let bv_solution = solver.eval_bitvec(&bv_value.get().inner)?;
                let py_solution = BV::new(py, &bv_solution)?
                    .into_any()
                    .downcast::<Base>()
                    .unwrap()
                    .clone();

                // Add constraint to exclude this solution if we aren't using a concrete solver
                // Kinda a hack, would like to do this in a better way
                if !matches!(self.inner, DynSolver::Concrete(_)) {
                    solver.add(&solver.context().neq(&bv_value.get().inner, &bv_solution)?)?;
                }

                py_solution
            } else if let Ok(bool_value) = expr.clone().into_any().downcast::<Bool>() {
                let bool_solution = solver.eval_bool(&bool_value.get().inner)?;
                let py_solution = Bool::new(py, &bool_solution)?
                    .into_any()
                    .downcast::<Base>()
                    .unwrap()
                    .clone();

                // Add constraint to exclude this solution if we aren't using a concrete solver
                // Kinda a hack, would like to do this in a better way
                if !matches!(self.inner, DynSolver::Concrete(_)) {
                    solver.add(
                        &solver
                            .context()
                            .neq(&bool_value.get().inner, &bool_solution)?,
                    )?;
                }

                py_solution
            } else if let Ok(fp_value) = expr.clone().into_any().downcast::<FP>() {
                let fp_solution = solver.eval_float(&fp_value.get().inner)?;
                let py_solution = FP::new(py, &fp_solution)?
                    .into_any()
                    .downcast::<Base>()
                    .unwrap()
                    .clone();

                // Add constraint to exclude this solution if we aren't using a concrete solver
                // Kinda a hack, would like to do this in a better way
                if !matches!(self.inner, DynSolver::Concrete(_)) {
                    solver.add(&solver.context().neq(&fp_value.get().inner, &fp_solution)?)?;
                }

                py_solution
            } else if let Ok(string_value) = expr.clone().into_any().downcast::<PyAstString>() {
                let string_solution = solver.eval_string(&string_value.get().inner)?;
                let py_solution = PyAstString::new(py, &string_solution)?
                    .into_any()
                    .downcast::<Base>()
                    .unwrap()
                    .clone();

                // Add constraint to exclude this solution if we aren't using a concrete solver
                // Kinda a hack, would like to do this in a better way
                if !matches!(self.inner, DynSolver::Concrete(_)) {
                    solver.add(
                        &solver
                            .context()
                            .neq(&string_value.get().inner, &string_solution)?,
                    )?;
                }

                py_solution
            } else {
                return Err(ClaripyError::TypeError("Unsupported type".to_string()));
            };

            // Add solution to results
            results.push(solution);
        }

        Ok(results)
    }

    #[pyo3(signature = (expr, n, extra_constraints = None, exact = None))]
    fn eval<'py>(
        &mut self,
        py: Python<'py>,
        expr: Bound<'py, Base>,
        n: u32,
        extra_constraints: Option<Vec<Bound<Bool>>>,
        exact: Option<Bound<'py, PyAny>>,
    ) -> PyResult<Vec<Bound<'py, PyAny>>> {
        self.eval_to_ast(py, expr, n, extra_constraints, exact)?
            .into_iter()
            .filter_map(|r| {
                if let Ok(bv_value) = r.clone().into_any().downcast::<BV>() {
                    // Assume that the BV is concrete, extract and return a Python integer
                    if let BitVecOp::BVV(bv) = bv_value.get().inner.op() {
                        Some(bv.to_biguint().into_bound_py_any(py))
                    } else {
                        None
                    }
                } else if let Ok(bool_value) = r.clone().into_any().downcast::<Bool>() {
                    // Assume that the Bool is concrete, extract and return a Python boolean
                    if let BooleanOp::BoolV(b) = bool_value.get().inner.op() {
                        Some(b.into_bound_py_any(py))
                    } else {
                        None
                    }
                } else if let Ok(fp_value) = r.clone().into_any().downcast::<FP>() {
                    // Assume that the FP is concrete, extract and return a Python float
                    if let FloatOp::FPV(fp) = fp_value.get().inner.op() {
                        fp.to_f64().map(|f| f.into_bound_py_any(py))
                    } else {
                        None
                    }
                } else if let Ok(string_value) = r.clone().into_any().downcast::<PyAstString>() {
                    // Assume that the PyAstString is concrete, extract and return a Python string
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
            .collect::<Result<Vec<Bound<PyAny>>, pyo3::PyErr>>()
    }

    #[pyo3(signature = (exprs, n, extra_constraints = None, exact = None))]
    fn batch_eval<'py>(
        &mut self,
        py: Python<'py>,
        exprs: Vec<Bound<'py, Base>>,
        n: u32,
        extra_constraints: Option<Vec<Bound<Bool>>>,
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
                solver.add(
                    &self
                        .inner
                        .context()
                        .eq_(&bool_ast.get().inner, &value.into())?,
                )?;
            } else {
                let value_type = value.get_type().name()?.extract::<String>()?;
                return Err(ClaripyError::TypeError(format!(
                    "can't coerce a {} to a bool ast",
                    value_type
                )));
            }
        } else if let Ok(bv_ast) = expr.downcast::<BV>() {
            if let Ok(value) = value.extract::<CoerceBV>() {
                solver.add(&self.inner.context().eq_(
                    &bv_ast.get().inner,
                    &value.extract_like(bv_ast.py(), bv_ast.get())?.get().inner,
                )?)?;
            } else {
                let value_type = value.get_type().name()?.extract::<String>()?;
                return Err(ClaripyError::TypeError(format!(
                    "can't coerce a {} to a bv ast",
                    value_type
                )));
            }
        } else if let Ok(fp_ast) = expr.downcast::<FP>() {
            if let Ok(value) = value.extract::<CoerceFP>() {
                solver.add(
                    &self
                        .inner
                        .context()
                        .eq_(&fp_ast.get().inner, &value.into())?,
                )?;
            } else {
                let value_type = value.get_type().name()?.extract::<String>()?;
                return Err(ClaripyError::TypeError(format!(
                    "can't coerce a {} to a float ast",
                    value_type
                )));
            }
        } else if let Ok(string_ast) = expr.downcast::<PyAstString>() {
            if let Ok(value) = value.extract::<CoerceString>() {
                solver.add(
                    &self
                        .inner
                        .context()
                        .eq_(&string_ast.get().inner, &value.into())?,
                )?;
            } else {
                let value_type = value.get_type().name()?.extract::<String>()?;
                return Err(ClaripyError::TypeError(format!(
                    "can't coerce a {} to a string ast",
                    value_type
                )));
            }
        } else {
            return Err(ClaripyError::TypeError(
                "expression must be a boolean, bitvector, float, or string".to_string(),
            ));
        }

        Ok(solver.satisfiable()?)
    }

    #[pyo3(signature = (expr, extra_constraints = None, exact = None))]
    fn is_true<'py>(
        &mut self,
        expr: Bound<Bool>,
        extra_constraints: Option<Vec<Bound<'py, Bool>>>,
        exact: Option<Bound<'py, PyAny>>,
    ) -> Result<bool, ClaripyError> {
        _ = exact; // TODO: Implement approximate solutions

        // Fork the solver for extra constraints
        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for expr in extra_constraints {
                solver.add(&expr.get().inner)?;
            }
        }
        Ok(solver.is_true(&expr.get().inner).unwrap())
    }

    #[pyo3(signature = (expr, extra_constraints = None, exact = None))]
    fn is_false<'py>(
        &mut self,
        expr: Bound<Bool>,
        extra_constraints: Option<Vec<Bound<'py, Bool>>>,
        exact: Option<Bound<'py, PyAny>>,
    ) -> Result<bool, ClaripyError> {
        _ = exact; // TODO: Implement approximate solutions

        // Fork the solver for extra constraints
        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for expr in extra_constraints {
                solver.add(&expr.get().inner)?;
            }
        }
        Ok(solver.is_false(&expr.get().inner).unwrap())
    }

    #[pyo3(signature = (expr, extra_constraints = None, exact = None, signed = false))]
    fn min<'py>(
        &mut self,
        expr: Bound<'py, BV>,
        extra_constraints: Option<Vec<Bound<'py, Bool>>>,
        exact: Option<Bound<'py, PyAny>>,
        signed: bool,
    ) -> Result<BigInt, ClaripyError> {
        let _ = exact; // TODO: Implement approximate solutions
        let _ = signed; // TODO: Implement signed solutions

        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for expr in extra_constraints {
                solver.add(&expr.get().inner)?;
            }
        }
        if let BitVecOp::BVV(bv) = solver.min(&expr.get().inner)?.op() {
            Ok(BigInt::from(bv.to_biguint()))
        } else {
            Err(ClaripyError::TypeError(
                "min: expression must be a bitvector".to_string(),
            ))
        }
    }

    #[pyo3(signature = (expr, extra_constraints = None, exact = None, signed = false))]
    fn max<'py>(
        &mut self,
        expr: Bound<'py, BV>,
        extra_constraints: Option<Vec<Bound<'py, Bool>>>,
        exact: Option<Bound<'py, PyAny>>,
        signed: bool,
    ) -> Result<BigInt, ClaripyError> {
        let _ = exact; // TODO: Implement approximate solutions
        let _ = signed; // TODO: Implement signedness

        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for expr in extra_constraints {
                solver.add(&expr.get().inner)?;
            }
        }

        if let BitVecOp::BVV(bv) = solver.max(&expr.get().inner)?.op() {
            Ok(BigInt::from(bv.to_biguint()))
        } else {
            Err(ClaripyError::TypeError(
                "min: expression must be a bitvector".to_string(),
            ))
        }
    }
}

#[pyclass(extends = PySolver, name = "ConcreteSolver", module = "clarirs.solver")]
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

#[pyclass(extends = PySolver, name = "Z3Solver", module = "clarirs.solver")]
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

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<PySolver>()?;
    m.add_class::<PyConcreteSolver>()?;
    m.add_class::<PyZ3Solver>()?;

    Ok(())
}
