#[macro_export]
macro_rules! add_pyfunctions {
    ($m:ident, $($fn_name:path),*,) => {
        $(
            $m.add_function(wrap_pyfunction!($fn_name, $m)?)?;
        )*
    };
}

#[macro_export]
macro_rules! pyop {
    // Match one argument
    ($m:ident, $fn_name:ident, $context_method:ident, $return_type:ty, $at:tt) => {
        #[allow(non_snake_case)]
        #[pyfunction]
        pub fn $fn_name(py: Python, ast: pyop!(@py? $at)) -> Result<Py<$return_type>, ClaripyError> {
            py_ast_from_astref(py, crate::ast::py_factory::GLOBAL_CONTEXT.$context_method(&crate::ast::get_astref(ast))?)
        }
    };

    // Match two arguments
    ($m:ident, $fn_name:ident, $context_method:ident, $return_type:ty, $at1:tt, $at2:tt) => {
        #[allow(non_snake_case)]
        #[pyfunction]
        pub fn $fn_name(py: Python, lhs: pyop!(@py? $at1), rhs: pyop!(@py? $at2)) -> Result<Py<$return_type>, ClaripyError> {
            py_ast_from_astref(py, crate::ast::py_factory::GLOBAL_CONTEXT.$context_method(&crate::ast::get_astref(lhs), &crate::ast::get_astref(rhs))?)
        }
    };

    // Extract-shaped
    // TODO: Why can't the named arguments pattern cover this?
    ($m:ident, $fn_name:ident, $context_method:ident, $return_type:ty, $at:ty, $a1:ident: $a1_t:tt, $a2:ident: $a2_t:tt) => {
        #[allow(non_snake_case)]
        #[pyfunction]
        pub fn $fn_name(py: Python, ast: PyRef<$at>, $a1: $a1_t, $a2: $a2_t) -> Result<Py<$return_type>, ClaripyError> {
            py_ast_from_astref(py, GLOBAL_CONTEXT.$context_method(&get_astref(ast), $a1, $a2)?)
        }
    };

    // If-shaped
    // TODO: Why can't the named arguments pattern cover this?
    ($m:ident, $fn_name:ident, $context_method:ident, $return_type:ty, $a1:ident: $a1_t:tt, $a2:ident: $a2_t:tt, $a3:ident, $a3_t:tt) => {
        #[allow(non_snake_case)]
        #[pyfunction]
        pub fn $fn_name(py: Python, ast: PyRef<$at>, $a1: pyop!(@py? $a1_t), $a2: pyop!(@py? $a2_t), $a3: pyop!(@py? $a3_t)) -> Result<Py<$return_type>, ClaripyError> {
            py_ast_from_astref(py, GLOBAL_CONTEXT.$context_method(&get_astref($a1), &get_astref($a2), &get_astref($a3))?)
        }
    };

    // Named arguments
    ($m:ident, $fn_name:ident, $context_method:ident, $return_type:ty, $($arg_name:ident: $arg_type:tt),*) => {
        #[pyfunction]
        #[allow(non_snake_case)]
        pub fn $fn_name(py: Python, $($arg_name: pyop!(@py? $arg_type)),*) -> Result<Py<$return_type>, ClaripyError> {
            // $(let $arg_name = define_pyop!(@convert_arg $arg_name, $arg_type);)*
            py_ast_from_astref(py, crate::ast::py_factory::GLOBAL_CONTEXT.$context_method($(pyop!(@astref? $arg_name, $arg_type)),*)?)
        }
    };

    // Helper to convert PyRef arguments to AstRef using get_astref
    (@astref? $arg_name:ident, PyRef<$inner_type:tt>) => {
        &crate::ast::py_factory::get_astref($arg_name),
    };

    (@astref? $arg_name:ident, String) => {
        $arg_name
    };

    (@astref? $arg_name:ident, BigUint) => {
        &$arg_name
    };

    (@astref? $arg_name:ident, u32) => {
        $arg_name
    };

    (@astref? $arg_name:ident, $arg_type:ty) => {
        $arg_name
    };

    (@py? Bool) => {
        PyRef<Bool>
    };

    (@py? BV) => {
        PyRef<BV>
    };

    (@py? PyRef<$arg_type:tt>) => {
        PyRef<$arg_type>
    };

    (@py? $arg_type:ty) => {
        $arg_type
    };
}
