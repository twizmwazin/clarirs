//! Raw FFI bindings to the Z3 theorem prover.
//!
//! The bindings are automatically generated from Z3's C header files using bindgen.

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(clippy::all)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;
    use std::ptr;

    #[test]
    fn test_basic_solving() {
        unsafe {
            // Create context
            let cfg = mk_config();
            let ctx = mk_context(cfg);
            del_config(cfg);

            // Create solver
            let solver = mk_solver(ctx);
            solver_inc_ref(ctx, solver);

            // Create integer sort and variables
            let int_sort = mk_int_sort(ctx);
            let x_name = CString::new("x").unwrap();
            let y_name = CString::new("y").unwrap();
            let x = mk_const(ctx, mk_string_symbol(ctx, x_name.as_ptr()), int_sort);
            let y = mk_const(ctx, mk_string_symbol(ctx, y_name.as_ptr()), int_sort);

            // Create constraints: x > 0, y > 0, x + y == 3
            let zero = mk_int(ctx, 0, int_sort);
            let three = mk_int(ctx, 3, int_sort);

            let x_gt_0 = mk_gt(ctx, x, zero);
            let y_gt_0 = mk_gt(ctx, y, zero);
            let args = [x, y];
            let sum = mk_add(ctx, 2, args.as_ptr());
            let sum_eq_3 = mk_eq(ctx, sum, three);

            // Add constraints to solver
            solver_assert(ctx, solver, x_gt_0);
            solver_assert(ctx, solver, y_gt_0);
            solver_assert(ctx, solver, sum_eq_3);

            // Check satisfiability
            let result = solver_check(ctx, solver);
            assert_eq!(result, Lbool::True);

            // Get model and verify values
            let model = solver_get_model(ctx, solver);
            model_inc_ref(ctx, model);

            let mut x_val = ptr::null_mut();
            let mut y_val = ptr::null_mut();

            assert_eq!(model_eval(ctx, model, x, true, &mut x_val), true);
            assert_eq!(model_eval(ctx, model, y, true, &mut y_val), true);

            let mut x_int: i32 = 0;
            let mut y_int: i32 = 0;
            assert_eq!(get_numeral_int(ctx, x_val, &mut x_int), true);
            assert_eq!(get_numeral_int(ctx, y_val, &mut y_int), true);

            // Values should be positive and sum to 3
            assert!(x_int > 0);
            assert!(y_int > 0);
            assert_eq!(x_int + y_int, 3);

            // Cleanup
            model_dec_ref(ctx, model);
            solver_dec_ref(ctx, solver);
            del_context(ctx);
        }
    }
}
