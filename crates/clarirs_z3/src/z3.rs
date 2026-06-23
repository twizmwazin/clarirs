//! Compatibility layer over the upstream [`z3-sys`] crate.
//!
//! Historically this crate depended on an in-tree `clarirs-z3-sys` binding that
//! exposed the Z3 C API with the `Z3_` prefix stripped from every function and
//! with the opaque handle types spelled in `PascalCase`. The upstream
//! [`z3-sys`] crate keeps the `Z3_` prefix on its functions and handle types but
//! otherwise uses the exact same `PascalCase` spelling for its enum variants, so
//! the only thing this module needs to do is re-export the upstream items under
//! the names the rest of `clarirs_z3` already uses.
//!
//! Two upstream API properties differ from the old in-tree bindings and are
//! handled at the call sites rather than here:
//!
//! * Every Z3 function that returns a pointer returns `Option<NonNull<…>>`
//!   instead of a raw (possibly null) pointer. Results destined for an
//!   [`crate::rc::RcAst`] go through `RcAst::try_from(Option<…>)`; other handles
//!   are unwrapped with [`crate::require`].
//! * `Z3_lbool` is an integer with the `Z3_L_TRUE` / `Z3_L_FALSE` / `Z3_L_UNDEF`
//!   constants rather than an enum, so comparisons use those constants.
//!
//! [`z3-sys`]: https://crates.io/crates/z3-sys

#![allow(non_camel_case_types)]

// Enums (`AstKind`, `SortKind`, `DeclKind`, `ErrorCode`, …), the `Z3_lbool`
// integer type and its `Z3_L_*` constants, and the raw `Z3_`-prefixed functions
// and handle types all come through this glob unchanged.
pub use z3_sys::*;

// Opaque handle types, spelled the way the rest of the crate expects.
pub use z3_sys::{
    Z3_ast as Ast, Z3_ast_vector as AstVector, Z3_context as Context, Z3_lbool as Lbool,
    Z3_model as Model, Z3_optimize as Optimize, Z3_params as Params, Z3_solver as Solver,
    Z3_sort as Sort,
};

// Functions, with the `Z3_` prefix stripped to match the previous in-tree
// bindings.
pub use z3_sys::{
    Z3_ast_vector_dec_ref as ast_vector_dec_ref, Z3_ast_vector_get as ast_vector_get,
    Z3_ast_vector_inc_ref as ast_vector_inc_ref, Z3_ast_vector_size as ast_vector_size,
    Z3_dec_ref as dec_ref, Z3_del_config as del_config, Z3_fpa_get_ebits as fpa_get_ebits,
    Z3_fpa_get_sbits as fpa_get_sbits, Z3_func_decl_to_string as func_decl_to_string,
    Z3_get_app_arg as get_app_arg, Z3_get_app_decl as get_app_decl,
    Z3_get_app_num_args as get_app_num_args, Z3_get_ast_kind as get_ast_kind,
    Z3_get_bv_sort_size as get_bv_sort_size, Z3_get_decl_int_parameter as get_decl_int_parameter,
    Z3_get_decl_kind as get_decl_kind, Z3_get_decl_name as get_decl_name,
    Z3_get_error_code as get_error_code, Z3_get_error_msg as get_error_msg,
    Z3_get_numeral_double as get_numeral_double, Z3_get_numeral_string as get_numeral_string,
    Z3_get_sort as get_sort, Z3_get_sort_kind as get_sort_kind, Z3_get_string as get_string,
    Z3_get_symbol_string as get_symbol_string, Z3_inc_ref as inc_ref, Z3_is_string as is_string,
    Z3_mk_and as mk_and, Z3_mk_bool_sort as mk_bool_sort, Z3_mk_bv_sort as mk_bv_sort,
    Z3_mk_bv2int as mk_bv2int, Z3_mk_bvadd as mk_bvadd, Z3_mk_bvand as mk_bvand,
    Z3_mk_bvashr as mk_bvashr, Z3_mk_bvlshr as mk_bvlshr, Z3_mk_bvmul as mk_bvmul,
    Z3_mk_bvneg as mk_bvneg, Z3_mk_bvnot as mk_bvnot, Z3_mk_bvor as mk_bvor,
    Z3_mk_bvsdiv as mk_bvsdiv, Z3_mk_bvsge as mk_bvsge, Z3_mk_bvsgt as mk_bvsgt,
    Z3_mk_bvshl as mk_bvshl, Z3_mk_bvsle as mk_bvsle, Z3_mk_bvslt as mk_bvslt,
    Z3_mk_bvsrem as mk_bvsrem, Z3_mk_bvsub as mk_bvsub, Z3_mk_bvudiv as mk_bvudiv,
    Z3_mk_bvuge as mk_bvuge, Z3_mk_bvugt as mk_bvugt, Z3_mk_bvule as mk_bvule,
    Z3_mk_bvult as mk_bvult, Z3_mk_bvurem as mk_bvurem, Z3_mk_bvxor as mk_bvxor,
    Z3_mk_char_sort as mk_char_sort, Z3_mk_concat as mk_concat, Z3_mk_config as mk_config,
    Z3_mk_const as mk_const, Z3_mk_context as mk_context, Z3_mk_distinct as mk_distinct,
    Z3_mk_eq as mk_eq, Z3_mk_ext_rotate_left as mk_ext_rotate_left,
    Z3_mk_ext_rotate_right as mk_ext_rotate_right, Z3_mk_extract as mk_extract,
    Z3_mk_false as mk_false, Z3_mk_fpa_abs as mk_fpa_abs, Z3_mk_fpa_add as mk_fpa_add,
    Z3_mk_fpa_div as mk_fpa_div, Z3_mk_fpa_eq as mk_fpa_eq, Z3_mk_fpa_fp as mk_fpa_fp,
    Z3_mk_fpa_geq as mk_fpa_geq, Z3_mk_fpa_gt as mk_fpa_gt,
    Z3_mk_fpa_is_infinite as mk_fpa_is_infinite, Z3_mk_fpa_is_nan as mk_fpa_is_nan,
    Z3_mk_fpa_leq as mk_fpa_leq, Z3_mk_fpa_lt as mk_fpa_lt, Z3_mk_fpa_mul as mk_fpa_mul,
    Z3_mk_fpa_neg as mk_fpa_neg, Z3_mk_fpa_numeral_double as mk_fpa_numeral_double,
    Z3_mk_fpa_numeral_float as mk_fpa_numeral_float, Z3_mk_fpa_rna as mk_fpa_rna,
    Z3_mk_fpa_rne as mk_fpa_rne, Z3_mk_fpa_rtn as mk_fpa_rtn, Z3_mk_fpa_rtp as mk_fpa_rtp,
    Z3_mk_fpa_rtz as mk_fpa_rtz, Z3_mk_fpa_sort as mk_fpa_sort, Z3_mk_fpa_sqrt as mk_fpa_sqrt,
    Z3_mk_fpa_sub as mk_fpa_sub, Z3_mk_fpa_to_fp_bv as mk_fpa_to_fp_bv,
    Z3_mk_fpa_to_fp_float as mk_fpa_to_fp_float, Z3_mk_fpa_to_fp_signed as mk_fpa_to_fp_signed,
    Z3_mk_fpa_to_fp_unsigned as mk_fpa_to_fp_unsigned, Z3_mk_fpa_to_ieee_bv as mk_fpa_to_ieee_bv,
    Z3_mk_fpa_to_sbv as mk_fpa_to_sbv, Z3_mk_fpa_to_ubv as mk_fpa_to_ubv, Z3_mk_ge as mk_ge,
    Z3_mk_gt as mk_gt, Z3_mk_int_sort as mk_int_sort, Z3_mk_int_to_str as mk_int_to_str,
    Z3_mk_int2bv as mk_int2bv, Z3_mk_ite as mk_ite, Z3_mk_not as mk_not,
    Z3_mk_numeral as mk_numeral, Z3_mk_optimize as mk_optimize, Z3_mk_or as mk_or,
    Z3_mk_params as mk_params, Z3_mk_seq_concat as mk_seq_concat,
    Z3_mk_seq_contains as mk_seq_contains, Z3_mk_seq_extract as mk_seq_extract,
    Z3_mk_seq_index as mk_seq_index, Z3_mk_seq_length as mk_seq_length,
    Z3_mk_seq_prefix as mk_seq_prefix, Z3_mk_seq_replace as mk_seq_replace,
    Z3_mk_seq_sort as mk_seq_sort, Z3_mk_seq_suffix as mk_seq_suffix,
    Z3_mk_sign_ext as mk_sign_ext, Z3_mk_solver as mk_solver, Z3_mk_str_to_int as mk_str_to_int,
    Z3_mk_string as mk_string, Z3_mk_string_symbol as mk_string_symbol, Z3_mk_true as mk_true,
    Z3_mk_xor as mk_xor, Z3_mk_zero_ext as mk_zero_ext, Z3_model_dec_ref as model_dec_ref,
    Z3_model_eval as model_eval, Z3_model_inc_ref as model_inc_ref,
    Z3_optimize_assert as optimize_assert, Z3_optimize_assert_soft as optimize_assert_soft,
    Z3_optimize_check as optimize_check, Z3_optimize_dec_ref as optimize_dec_ref,
    Z3_optimize_get_model as optimize_get_model, Z3_optimize_inc_ref as optimize_inc_ref,
    Z3_optimize_maximize as optimize_maximize, Z3_optimize_minimize as optimize_minimize,
    Z3_params_dec_ref as params_dec_ref, Z3_params_inc_ref as params_inc_ref,
    Z3_params_set_bool as params_set_bool, Z3_params_set_uint as params_set_uint,
    Z3_set_error_handler as set_error_handler, Z3_simplify as simplify,
    Z3_solver_assert as solver_assert, Z3_solver_assert_and_track as solver_assert_and_track,
    Z3_solver_check as solver_check, Z3_solver_check_assumptions as solver_check_assumptions,
    Z3_solver_dec_ref as solver_dec_ref, Z3_solver_get_model as solver_get_model,
    Z3_solver_get_unsat_core as solver_get_unsat_core, Z3_solver_inc_ref as solver_inc_ref,
    Z3_solver_set_params as solver_set_params, Z3_to_app as to_app,
};

// Only used by `#[cfg(test)]` helpers that construct standalone Z3 symbols.
#[cfg(test)]
pub use z3_sys::{Z3_mk_app as mk_app, Z3_mk_func_decl as mk_func_decl};
