use crate::prelude::*;

macro_rules! pysolver {
    ($m:ident, $pystruct:ident, $struct_:ident, $pyname:literal) => {
        #[pyclass(name = $pyname, module = "claripy.solver")]
        pub struct $pystruct {
            solver: $struct_<'static>,
        }

        #[pymethods]
        impl $pystruct {
            #[new]
            fn new() -> Result<PyClassInitializer<Self>, ClaripyError> {
                Ok(PyClassInitializer::from(Self {
                    solver: $struct_::new(&GLOBAL_CONTEXT)?,
                }))
            }

            fn add(&mut self, expr: Bound<Base>) -> Result<(), ClaripyError> {
                Ok(self.solver.add(&expr.get().ast.clone())?)
            }

            fn eval(&mut self, py: Python, expr: Bound<Base>) -> Result<Py<Base>, ClaripyError> {
                py_ast_from_astref(py, self.solver.eval(&expr.get().ast)?)
            }

            fn batch_eval(
                &mut self,
                py: Python,
                exprs: Vec<Bound<Base>>,
                max_solutions: u32,
            ) -> Result<Vec<Py<Base>>, ClaripyError> {
                self.solver
                    .batch_eval(exprs.iter().map(|e| e.get().ast.clone()), max_solutions)?
                    .into_iter()
                    .map(|ast| py_ast_from_astref::<Base>(py, ast))
                    .collect::<Result<Vec<Py<Base>>, ClaripyError>>()
            }

            fn is_solution(
                &mut self,
                expr: Bound<Base>,
                value: Bound<Base>,
            ) -> Result<bool, ClaripyError> {
                Ok(self.solver.is_solution(&expr.get().ast, &value.get().ast)?)
            }

            fn is_true(&mut self, expr: Bound<Base>) -> Result<bool, ClaripyError> {
                Ok(self.solver.is_true(&expr.get().ast).unwrap())
            }

            fn is_false(&mut self, expr: Bound<Base>) -> Result<bool, ClaripyError> {
                Ok(self.solver.is_false(&expr.get().ast).unwrap())
            }

            fn min(&mut self, py: Python, expr: Bound<Base>) -> Result<Py<Base>, ClaripyError> {
                py_ast_from_astref(py, self.solver.min(expr.get().ast.clone()).unwrap())
            }

            fn max(&mut self, py: Python, expr: Bound<Base>) -> Result<Py<Base>, ClaripyError> {
                py_ast_from_astref(py, self.solver.max(expr.get().ast.clone()).unwrap())
            }
        }
        $m.add_class::<PyConcreteSolver>()?;
    };
}

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    pysolver!(m, PyConcreteSolver, ConcreteSolver, "ConcreteSolver");
    Ok(())
}
