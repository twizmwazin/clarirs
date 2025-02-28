use crate::{dynsolver::DynSolver, prelude::*};
use clarirs_z3::Z3Solver;

#[pyclass(name = "Solver", module = "clarirs.solver", subclass)]
pub struct PySolver {
    inner: DynSolver,
}

#[pymethods]
impl PySolver {
    fn add<'py>(
        &mut self,
        exprs: Vec<Bound<'py, Bool>>,
    ) -> Result<Vec<Bound<'py, Bool>>, ClaripyError> {
        for expr in exprs.clone() {
            self.inner.add(&expr.get().inner)?;
        }
        Ok(exprs)
    }

    fn satisfiable(&mut self) -> Result<bool, ClaripyError> {
        Ok(self.inner.satisfiable().unwrap())
    }

    #[pyo3(signature = (expr, n, extra_constraints = None, exact = None))]
    fn eval_to_ast(
        &mut self,
        py: Python,
        expr: Bound<Base>,
        n: u32,
        extra_constraints: Option<Vec<Bound<Bool>>>,
        exact: Option<Bound<'_, PyAny>>,
    ) -> Result<Vec<Py<Base>>, ClaripyError> {
        let _ = n; // TODO: Implement multiple solutions
        let _ = exact; // TODO: Implement approximate solutions

        // Fork the solver for extra constraints
        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for expr in extra_constraints {
                solver.add(&expr.get().inner)?;
            }
        }

        if let Ok(bv_value) = expr.clone().into_any().downcast::<BV>() {
            BV::new(py, &solver.eval_bitvec(&bv_value.get().inner)?).map(|b| {
                b.into_any()
                    .downcast_bound::<Base>(py)
                    .unwrap()
                    .clone()
                    .unbind()
            })
        } else if let Ok(bool_value) = expr.clone().into_any().downcast::<Bool>() {
            Bool::new(py, &solver.eval_bool(&bool_value.get().inner).unwrap()).map(|b| {
                b.into_any()
                    .downcast_bound::<Base>(py)
                    .unwrap()
                    .clone()
                    .unbind()
            })
        } else if let Ok(fp_value) = expr.clone().into_any().downcast::<FP>() {
            FP::new(py, &solver.eval_float(&fp_value.get().inner)?).map(|b| {
                b.into_any()
                    .downcast_bound::<Base>(py)
                    .unwrap()
                    .clone()
                    .unbind()
            })
        } else if let Ok(string_value) = expr.clone().into_any().downcast::<PyAstString>() {
            PyAstString::new(py, &solver.eval_string(&string_value.get().inner)?).map(|b| {
                b.into_any()
                    .downcast_bound::<Base>(py)
                    .unwrap()
                    .clone()
                    .unbind()
            })
        } else {
            panic!("Unsupported type");
        }
        .map(|b| vec![b])
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
                if let Ok(bv_value) = r.clone().into_any().downcast_bound::<BV>(py) {
                    // Assume that the BV is concrete, extract and return a Python integer
                    if let BitVecOp::BVV(bv) = bv_value.get().inner.op() {
                        Some(bv.to_biguint().into_bound_py_any(py))
                    } else {
                        None
                    }
                } else if let Ok(bool_value) = r.clone().into_any().downcast_bound::<Bool>(py) {
                    // Assume that the Bool is concrete, extract and return a Python boolean
                    if let BooleanOp::BoolV(b) = bool_value.get().inner.op() {
                        Some(b.into_bound_py_any(py))
                    } else {
                        None
                    }
                } else if let Ok(fp_value) = r.clone().into_any().downcast_bound::<FP>(py) {
                    // Assume that the FP is concrete, extract and return a Python float
                    if let FloatOp::FPV(fp) = fp_value.get().inner.op() {
                        fp.to_f64().map(|f| f.into_bound_py_any(py))
                    } else {
                        None
                    }
                } else if let Ok(string_value) =
                    r.clone().into_any().downcast_bound::<PyAstString>(py)
                {
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

    fn is_true(&mut self, expr: Bound<Bool>) -> Result<bool, ClaripyError> {
        Ok(self.inner.is_true(&expr.get().inner).unwrap())
    }

    fn is_false(&mut self, expr: Bound<Bool>) -> Result<bool, ClaripyError> {
        Ok(self.inner.is_false(&expr.get().inner).unwrap())
    }

    #[pyo3(signature = (expr, extra_constraints = None, exact = None, signed = false))]
    fn min(
        &mut self,
        py: Python,
        expr: Bound<BV>,
        extra_constraints: Option<Vec<Bound<Bool>>>,
        exact: Option<Bound<PyAny>>,
        signed: bool,
    ) -> Result<Py<BV>, ClaripyError> {
        let _ = exact; // TODO: Implement approximate solutions
        let _ = signed; // TODO: Implement signed solutions

        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for expr in extra_constraints {
                solver.add(&expr.get().inner)?;
            }
        }
        BV::new(py, &solver.min(&expr.get().inner).unwrap())
    }

    #[pyo3(signature = (expr, extra_constraints = None, exact = None, signed = false))]
    fn max(
        &mut self,
        py: Python,
        expr: Bound<BV>,
        extra_constraints: Option<Vec<Bound<Bool>>>,
        exact: Option<Bound<PyAny>>,
        signed: bool,
    ) -> Result<Py<BV>, ClaripyError> {
        let _ = exact; // TODO: Implement approximate solutions
        let _ = signed; // TODO: Implement signedness

        let mut solver = self.inner.clone();
        if let Some(extra_constraints) = extra_constraints {
            for expr in extra_constraints {
                solver.add(&expr.get().inner)?;
            }
        }
        BV::new(py, &solver.max(&expr.get().inner).unwrap())
    }
}

#[pyclass(extends = PySolver, name = "ConcreteSolver", module = "clarirs.solver")]
pub struct PyConcreteSolver;

#[pymethods]
impl PyConcreteSolver {
    #[new]
    fn new() -> Result<PyClassInitializer<Self>, ClaripyError> {
        Ok(PyClassInitializer::from(PySolver {
            inner: DynSolver::ConcreteSolver(ConcreteSolver::new(&GLOBAL_CONTEXT)),
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
            inner: DynSolver::Z3Solver(Z3Solver::new(&GLOBAL_CONTEXT)),
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
