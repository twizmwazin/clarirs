use std::{
    collections::HashMap,
    sync::{LazyLock, RwLock},
};

use pyo3::pyclass_init::PyObjectInit;

use crate::prelude::*;

pub static GLOBAL_CONTEXT: LazyLock<Context<'static>> = LazyLock::new(Context::new);
pub static PY_OBJECT_CACHE: LazyLock<RwLock<HashMap<u64, WeakRef>>> =
    LazyLock::new(|| RwLock::new(HashMap::new()));

pub fn extract_arg<'py, T>(
    py: Python<'py>,
    args: &[PyObject],
    index: usize,
) -> Result<T, ClaripyError>
where
    T: FromPyObject<'py>,
{
    args.get(index)
        .ok_or(ClaripyError::MissingArgIndex(index))
        .and_then(|arg| {
            arg.extract::<T>(py)
                .map_err(|_| ClaripyError::FailedToExtractArg(arg.clone_ref(py)))
        })
}

pub fn py_ast_from_astref<T>(py: Python, native_ast: AstRef<'static>) -> Result<Py<T>, ClaripyError>
where
    T: PyAst,
{
    let cached_obj = PY_OBJECT_CACHE
        .read()
        .unwrap()
        .get(&native_ast.hash())
        .and_then(|weak_ptr| weak_ptr.upgrade(py));
    match cached_obj {
        Some(py_obj) => Ok(py_obj),
        None => {
            let py_init = T::new_from_astref(&native_ast);
            let py_obj = unsafe {
                Py::from_owned_ptr(py, py_init.into_new_object(py, T::type_object_raw(py))?)
            };
            let weakref = WeakRef::from(&py_obj);
            PY_OBJECT_CACHE
                .write()
                .unwrap()
                .insert(native_ast.hash(), weakref);
            Ok(py_obj)
        }
    }
}
