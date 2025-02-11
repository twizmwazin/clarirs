use crate::prelude::*;

#[pyclass(name = "ConcreteSolver", module = "clarirs.solver")]
pub struct PyConcreteSolver {
    inner: ConcreteSolver<'static>,
}

#[pymethods]
impl PyConcreteSolver {
    #[new]
    fn new() -> Result<PyClassInitializer<Self>, ClaripyError> {
        Ok(PyClassInitializer::from(Self {
            inner: ConcreteSolver::new(&GLOBAL_CONTEXT)?,
        }))
    }

    fn add(&mut self, expr: Bound<Bool>) -> Result<(), ClaripyError> {
        Ok(self.inner.add(&expr.get().inner)?)
    }

    fn eval(&mut self, py: Python, expr: Bound<Base>) -> Result<Py<Base>, ClaripyError> {
        if let Ok(bv_value) = expr.clone().into_any().downcast::<BV>() {
            BV::new(py, &self.inner.eval_bitvec(&bv_value.get().inner)?).map(|b| {
                b.into_any()
                    .downcast_bound::<Base>(py)
                    .unwrap()
                    .clone()
                    .unbind()
            })
        } else if let Ok(bool_value) = expr.clone().into_any().downcast::<Bool>() {
            Bool::new(py, &self.inner.eval_bool(&bool_value.get().inner).unwrap()).map(|b| {
                b.into_any()
                    .downcast_bound::<Base>(py)
                    .unwrap()
                    .clone()
                    .unbind()
            })
        } else if let Ok(fp_value) = expr.clone().into_any().downcast::<FP>() {
            FP::new(py, &self.inner.eval_float(&fp_value.get().inner)?).map(|b| {
                b.into_any()
                    .downcast_bound::<Base>(py)
                    .unwrap()
                    .clone()
                    .unbind()
            })
        } else if let Ok(string_value) = expr.clone().into_any().downcast::<PyAstString>() {
            PyAstString::new(py, &self.inner.eval_string(&string_value.get().inner)?).map(|b| {
                b.into_any()
                    .downcast_bound::<Base>(py)
                    .unwrap()
                    .clone()
                    .unbind()
            })
        } else {
            panic!("Unsupported type");
        }
    }

    fn batch_eval(
        &mut self,
        py: Python,
        exprs: Vec<Bound<Base>>,
        _max_solutions: u32, // Concrete solver does not support multiple solutions
    ) -> Result<Vec<Py<Base>>, ClaripyError> {
        exprs.into_iter().map(|expr| self.eval(py, expr)).collect()
    }

    fn is_true(&mut self, expr: Bound<Bool>) -> Result<bool, ClaripyError> {
        Ok(self.inner.is_true(&expr.get().inner).unwrap())
    }

    fn is_false(&mut self, expr: Bound<Bool>) -> Result<bool, ClaripyError> {
        Ok(self.inner.is_false(&expr.get().inner).unwrap())
    }

    fn min(&mut self, py: Python, expr: Bound<BV>) -> Result<Py<BV>, ClaripyError> {
        BV::new(py, &self.inner.min(&expr.get().inner).unwrap())
    }

    fn max(&mut self, py: Python, expr: Bound<BV>) -> Result<Py<BV>, ClaripyError> {
        BV::new(py, &self.inner.max(&expr.get().inner).unwrap())
    }
}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<PyConcreteSolver>()?;
    Ok(())
}
