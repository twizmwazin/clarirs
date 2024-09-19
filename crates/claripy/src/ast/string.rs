#![allow(non_snake_case)]

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
// pyop!(StrSubstr, strsubstr, AstString, AstString, BV, BV);
pyop!(StrContains, strcontains, AstString, AstString, AstString);
pyop!(StrIndexOf, strindexof, AstString, AstString, AstString);
// pyop!(StrReplace, strreplace, AstString, AstString, AstString, AstString);
pyop!(StrPrefixOf, strprefixof, AstString, AstString, AstString);
pyop!(StrSuffixOf, strsuffixof, AstString, AstString, AstString);
// pyop!(StrToBV, strtobv, BV, AstString, u32);
// pyop!(BVToStr, bvtostr, AstString, BV);
pyop!(StrIsDigit, strisdigit, AstString, AstString);
pyop!(StrEq, streq, AstString, AstString, AstString);
pyop!(StrNeq, strneq, AstString, AstString, AstString);

pub(crate) fn import<'py>(_: Python, m: &Bound<'py, PyModule>) -> PyResult<()> {
    m.add_class::<AstString>()?;

    add_pyfunctions!(
        m,
        StringS,
        StringV,
        StrLen,
        StrConcat,
        // StrSubstr,
        StrContains,
        StrIndexOf,
        // StrReplace,
        StrPrefixOf,
        StrSuffixOf,
        // StrToBV,
        // BVToStr,
        StrIsDigit,
        StrEq,
        StrNeq,
    );

    Ok(())
}
