use clarirs_z3_sys as z3;
use std::ffi::CString;
use std::ptr;

fn main() {
    unsafe {
        // Create context
        let cfg = z3::mk_config();
        let ctx = z3::mk_context(cfg);
        z3::del_config(cfg);

        // Create solver
        let solver = z3::mk_solver(ctx);
        z3::solver_inc_ref(ctx, solver);

        // Create integer sort and variables
        let int_sort = z3::mk_int_sort(ctx);
        let x_name = CString::new("x").unwrap();
        let y_name = CString::new("y").unwrap();
        let x = z3::mk_const(ctx, z3::mk_string_symbol(ctx, x_name.as_ptr()), int_sort);
        let y = z3::mk_const(ctx, z3::mk_string_symbol(ctx, y_name.as_ptr()), int_sort);

        // Create constraints: x > 0, y > 0, x + y == 3
        let zero = z3::mk_int(ctx, 0, int_sort);
        let three = z3::mk_int(ctx, 3, int_sort);

        let x_gt_0 = z3::mk_gt(ctx, x, zero);
        let y_gt_0 = z3::mk_gt(ctx, y, zero);
        let args = [x, y];
        let sum = z3::mk_add(ctx, 2, args.as_ptr());
        let sum_eq_3 = z3::mk_eq(ctx, sum, three);

        // Add constraints to solver
        z3::solver_assert(ctx, solver, x_gt_0);
        z3::solver_assert(ctx, solver, y_gt_0);
        z3::solver_assert(ctx, solver, sum_eq_3);

        // Check satisfiability
        let result = z3::solver_check(ctx, solver);
        println!("Satisfiable: {}", result == z3::Lbool::True);

        if result == z3::Lbool::True {
            // Get model and print values
            let model = z3::solver_get_model(ctx, solver);
            z3::model_inc_ref(ctx, model);

            let mut x_val = ptr::null_mut();
            let mut y_val = ptr::null_mut();

            z3::model_eval(ctx, model, x, true, &mut x_val);
            z3::model_eval(ctx, model, y, true, &mut y_val);

            let mut x_int: i32 = 0;
            let mut y_int: i32 = 0;
            z3::get_numeral_int(ctx, x_val, &mut x_int);
            z3::get_numeral_int(ctx, y_val, &mut y_int);

            println!("Solution found:");
            println!("x = {x_int}");
            println!("y = {y_int}");
            println!("Sum = {}", x_int + y_int);

            // Cleanup
            z3::model_dec_ref(ctx, model);
        }

        // Cleanup
        z3::solver_dec_ref(ctx, solver);
        z3::del_context(ctx);
    }
}
