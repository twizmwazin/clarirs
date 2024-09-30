#![allow(non_snake_case)]

use ast::bv::BV;

use crate::ast::bits::Bits;
use crate::prelude::*;

#[pyclass(name="String", extends=Bits, subclass, frozen, module="claripy.ast.string")]
pub struct AstString;

impl PyAst for AstString {
    fn new_from_astref(ast_ref: &AstRef<'static>) -> PyClassInitializer<Self> {
        Bits::new_from_astref(ast_ref).add_subclass(AstString {})
    }

    fn as_base(self_: PyRef<Self>) -> PyRef<Base> {
        self_.into_super().into_super()
    }
}

pyop!(StringS, strings, AstString, name: String, size: u32);
pyop!(StringV, stringv, AstString, value: String);
pyop!(StrLen, strlen, AstString, AstString);
pyop!(StrConcat, strconcat, AstString, AstString, AstString);

#[pyfunction]
pub fn StrSubstr(
    py: Python,
    base: PyRef<AstString>,
    start: PyRef<BV>,
    end: PyRef<BV>,
) -> Result<Py<AstString>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.strsubstr(&get_astref(base), &get_astref(start), &get_astref(end))?,
    )
}

pyop!(StrContains, strcontains, AstString, AstString, AstString);

#[pyfunction]
pub fn StrIndexOf(
    py: Python,
    haystack: PyRef<AstString>,
    needle: PyRef<AstString>,
    start: PyRef<BV>,
) -> Result<Py<BV>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.strindexof(
            &get_astref(haystack),
            &get_astref(needle),
            &get_astref(start),
        )?,
    )
}

#[pyfunction]
pub fn StrReplace(
    py: Python,
    haystack: PyRef<AstString>,
    needle: PyRef<AstString>,
    replacement: PyRef<AstString>,
) -> Result<Py<AstString>, ClaripyError> {
    py_ast_from_astref(
        py,
        GLOBAL_CONTEXT.strreplace(
            &get_astref(haystack),
            &get_astref(needle),
            &get_astref(replacement),
        )?,
    )
}

pyop!(StrPrefixOf, strprefixof, AstString, AstString, AstString);
pyop!(StrSuffixOf, strsuffixof, AstString, AstString, AstString);

#[pyfunction]
pub fn StrToBV(py: Python, s: PyRef<AstString>) -> Result<Py<BV>, ClaripyError> {
    py_ast_from_astref(py, GLOBAL_CONTEXT.strtobv(&get_astref(s))?)
}

#[pyfunction]
pub fn BVToStr(py: Python, bv: PyRef<BV>) -> Result<Py<AstString>, ClaripyError> {
    py_ast_from_astref(py, GLOBAL_CONTEXT.bvtostr(&get_astref(bv))?)
}

pyop!(StrIsDigit, strisdigit, AstString, AstString);
pyop!(StrEq, streq, AstString, AstString, AstString);
pyop!(StrNeq, strneq, AstString, AstString, AstString);

pub(crate) fn import(_: Python, m: &Bound<PyModule>) -> PyResult<()> {
    m.add_class::<AstString>()?;

    add_pyfunctions!(
        m,
        StringS,
        StringV,
        StrLen,
        StrConcat,
        StrSubstr,
        StrContains,
        StrIndexOf,
        StrReplace,
        StrPrefixOf,
        StrSuffixOf,
        StrToBV,
        BVToStr,
        StrIsDigit,
        StrEq,
        StrNeq,
    );

    Ok(())
}
