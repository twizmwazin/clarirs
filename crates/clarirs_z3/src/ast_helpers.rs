#![allow(dead_code)]

use std::ffi::CStr;

use crate::{Z3_CONTEXT, checked_ast};
use crate::z3_compat as z3;

/// Returns the `DeclKind` of a Z3 AST node (assumes it is an application).
pub fn decl_kind(ast: z3::Ast) -> z3::DeclKind {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let app = z3::to_app(ctx, ast);
        let decl = z3::get_app_decl(ctx, app);
        z3::get_decl_kind(ctx, decl)
    })
}

/// Returns the number of arguments (assumes it is an application).
pub fn num_args(ast: z3::Ast) -> u32 {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let app = z3::to_app(ctx, ast);
        z3::get_app_num_args(ctx, app)
    })
}

/// Returns the argument at `index` as a new AST, or `None` if out of
/// bounds or the node is not an application.
pub fn arg(ast: z3::Ast, index: u32) -> Option<z3::Ast> {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let ast_kind = z3::get_ast_kind(ctx, ast);
        if ast_kind != z3::AstKind::App {
            return None;
        }
        let app = z3::to_app(ctx, ast);
        let n = z3::get_app_num_args(ctx, app);
        if index >= n {
            return None;
        }
        checked_ast(z3::get_app_arg(ctx, app, index)).ok()
    })
}

/// Returns the symbol name if this is an uninterpreted constant, or `None`
/// otherwise.
pub fn symbol_name(ast: z3::Ast) -> Option<String> {
    Z3_CONTEXT.with(|&ctx| unsafe {
        if z3::get_ast_kind(ctx, ast) != z3::AstKind::App {
            return None;
        }
        let app = z3::to_app(ctx, ast);
        let decl = z3::get_app_decl(ctx, app);
        if z3::get_decl_kind(ctx, decl) != z3::DeclKind::Uninterpreted {
            return None;
        }
        let sym = z3::get_decl_name(ctx, decl);
        let name = z3::get_symbol_string(ctx, sym);
        CStr::from_ptr(name).to_str().ok().map(|s| s.to_owned())
    })
}

/// Creates an uninterpreted constant with the given name and sort.
#[cfg(test)]
pub fn mk_symbol(name: &str, sort: z3::Sort) -> z3::Ast {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let c_name = std::ffi::CString::new(name).unwrap();
        let sym = z3::mk_string_symbol(ctx, c_name.as_ptr());
        let decl = z3::mk_func_decl(ctx, sym, 0, std::ptr::null(), sort);
        checked_ast(z3::mk_app(ctx, decl, 0, std::ptr::null())).unwrap()
    })
}

/// Creates a Z3 boolean symbol.
#[cfg(test)]
pub fn mk_bool(name: &str) -> z3::Ast {
    Z3_CONTEXT.with(|&ctx| unsafe { mk_symbol(name, z3::mk_bool_sort(ctx)) })
}

/// Creates a Z3 bitvector symbol.
#[cfg(test)]
pub fn mk_bv(name: &str, width: u32) -> z3::Ast {
    Z3_CONTEXT.with(|&ctx| unsafe { mk_symbol(name, z3::mk_bv_sort(ctx, width)) })
}

/// Creates a Z3 floating-point symbol. Z3's sbits includes the implicit
/// leading bit, so `mantissa + 1` is passed to `mk_fpa_sort`.
#[cfg(test)]
pub fn mk_fp(name: &str, sort: clarirs_core::prelude::FSort) -> z3::Ast {
    Z3_CONTEXT.with(|&ctx| unsafe {
        mk_symbol(name, z3::mk_fpa_sort(ctx, sort.exponent, sort.mantissa + 1))
    })
}

/// Creates a Z3 bitvector numeral from a decimal string value and width.
#[cfg(test)]
pub fn mk_bv_val(value: &str, width: u32) -> z3::Ast {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let sort = z3::mk_bv_sort(ctx, width);
        let c_val = std::ffi::CString::new(value).unwrap();
        checked_ast(z3::mk_numeral(ctx, c_val.as_ptr(), sort)).unwrap()
    })
}

/// Creates a Z3 floating-point numeral from an `f32`.
#[cfg(test)]
pub fn mk_fp_val_f32(value: f32) -> z3::Ast {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let sort = z3::mk_fpa_sort(ctx, 8, 24);
        checked_ast(z3::mk_fpa_numeral_float(ctx, value, sort)).unwrap()
    })
}

/// Creates a Z3 floating-point numeral from an `f64`.
#[cfg(test)]
pub fn mk_fp_val_f64(value: f64) -> z3::Ast {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let sort = z3::mk_fpa_sort(ctx, 11, 53);
        checked_ast(z3::mk_fpa_numeral_double(ctx, value, sort)).unwrap()
    })
}

/// Creates a Z3 rounding mode AST.
#[cfg(test)]
pub fn mk_fprm(rm: clarirs_core::prelude::FPRM) -> z3::Ast {
    use clarirs_core::prelude::FPRM;
    Z3_CONTEXT.with(|&ctx| unsafe {
        checked_ast(match rm {
            FPRM::NearestTiesToEven => z3::mk_fpa_rne(ctx),
            FPRM::TowardPositive => z3::mk_fpa_rtp(ctx),
            FPRM::TowardNegative => z3::mk_fpa_rtn(ctx),
            FPRM::TowardZero => z3::mk_fpa_rtz(ctx),
            FPRM::NearestTiesToAway => z3::mk_fpa_rna(ctx),
        })
        .unwrap()
    })
}

/// Creates a Z3 string (sequence of chars) symbol.
#[cfg(test)]
pub fn mk_string(name: &str) -> z3::Ast {
    Z3_CONTEXT.with(|&ctx| unsafe {
        mk_symbol(name, z3::mk_seq_sort(ctx, z3::mk_char_sort(ctx)))
    })
}

/// Creates a Z3 string constant (literal value).
#[cfg(test)]
pub fn mk_string_val(value: &str) -> z3::Ast {
    Z3_CONTEXT.with(|&ctx| unsafe {
        let c_val = std::ffi::CString::new(value).unwrap();
        checked_ast(z3::mk_string(ctx, c_val.as_ptr())).unwrap()
    })
}
