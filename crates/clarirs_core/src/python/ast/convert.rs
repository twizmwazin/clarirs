//! Direct conversions between the core AST and Python objects.
//!
//! These impls are the point of hosting the bindings inside `clarirs_core`. We
//! would like to implement PyO3's `IntoPyObject`/`FromPyObject` straight onto
//! [`AstRef`], but `AstRef` is `Arc<AstNode>`, and `Arc` is a foreign,
//! non-`#[fundamental]` type, so the orphan rule still treats `Arc<AstNode>` as
//! foreign. [`PyAst`] is the minimal local newtype those impls hang on.
//!
//! With it, a `#[pyfunction]` can take and return ASTs as `PyAst` and let PyO3
//! wrap/unwrap them automatically — replacing the `Base::from_ast` / `X::new` /
//! `.into_any().cast::<Base>()` / `.get().inner.clone()` boilerplate that used
//! to appear at every boundary.

use pyo3::types::PyType;

use crate::python::prelude::*;

/// A Python-facing wrapper over an owned [`AstRef`]. Construct one with
/// `ast.into()` (or `PyAst(ast)`) to return an AST from a `#[pyfunction]`; take
/// one as a parameter to accept any Python AST object (or a coercible literal).
pub struct PyAst(pub AstRef<'static>);

impl From<AstRef<'static>> for PyAst {
    fn from(ast: AstRef<'static>) -> Self {
        PyAst(ast)
    }
}

impl From<PyAst> for AstRef<'static> {
    fn from(ast: PyAst) -> Self {
        ast.0
    }
}

/// Wrap an owned `AstRef` in the appropriate Python AST subclass (returned as
/// its `Base` view). This centralises the sort dispatch that used to be spelled
/// out at every boundary.
impl<'py> IntoPyObject<'py> for PyAst {
    type Target = Base;
    type Output = Bound<'py, Base>;
    type Error = ClaripyError;

    fn into_pyobject(self, py: Python<'py>) -> Result<Self::Output, Self::Error> {
        Base::from_ast(py, self.0)
    }
}

/// Extract the underlying `AstRef` from a Python AST object (a `Bool`, `BV`,
/// `FP`, or `String`). This is the strict counterpart to returning a `PyAst`:
/// it accepts exactly what a `Bound<Base>` parameter used to, with no literal
/// coercion. Contexts that coerce Python `int`/`bool`/`float`/`str` literals
/// keep using `CoerceBase`/`CoerceBV`/`CoerceFP`, which also handle sizing.
impl<'py> FromPyObject<'_, 'py> for PyAst {
    type Error = PyErr;

    fn extract(val: Borrowed<'_, 'py, PyAny>) -> PyResult<Self> {
        if let Ok(bool_val) = val.cast::<Bool>() {
            Ok(PyAst(bool_val.get().inner.clone()))
        } else if let Ok(bv_val) = val.cast::<BV>() {
            Ok(PyAst(bv_val.get().inner.clone()))
        } else if let Ok(fp_val) = val.cast::<FP>() {
            Ok(PyAst(fp_val.get().inner.clone()))
        } else if let Ok(string_val) = val.cast::<PyAstString>() {
            Ok(PyAst(string_val.get().inner.clone()))
        } else {
            Err(
                ClaripyError::InvalidArgumentType("Expected an AST: Bool, BV, FP, or String".to_string())
                    .into(),
            )
        }
    }
}

/// The `(callable, state)` pair Python uses to reconstruct an AST through
/// `copy`/`pickle`: calling `Class(op, args, annotations)`. Spelled out, this
/// type is a dozen lines of nested generics; naming it keeps each subclass's
/// `__reduce__` to a single line.
pub type ReduceResult<'py> = Result<
    (
        Bound<'py, PyAny>,
        (
            String,
            Vec<Bound<'py, PyAny>>,
            Vec<Bound<'py, PyAnnotation>>,
        ),
    ),
    ClaripyError,
>;

/// Shared body for every AST subclass's `__reduce__`: reconstruct via
/// `class(op_string, py_args, annotations)`.
pub fn ast_reduce<'py>(
    py: Python<'py>,
    class: Bound<'py, PyType>,
    inner: &AstRef<'static>,
) -> ReduceResult<'py> {
    let op = inner.to_opstring();
    let args = inner.extract_py_args(py)?;
    let annotations = inner
        .annotations()
        .iter()
        .map(|annotation| PyAnnotation::from_annotation(py, annotation))
        .collect::<Result<_, _>>()?;
    Ok((class.into_any(), (op, args, annotations)))
}
