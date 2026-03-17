use std::hint::black_box;
use std::time::Instant;

use clarirs_core::algorithms::Replace;
use clarirs_core::prelude::*;

// ============================================================================
// Benchmark harness
// ============================================================================

fn bench<F: FnMut()>(name: &str, iters: u64, mut f: F) {
    // Warmup
    for _ in 0..std::cmp::min(iters / 10, 100) {
        f();
    }

    let start = Instant::now();
    for _ in 0..iters {
        f();
    }
    let elapsed = start.elapsed();

    let per_iter = elapsed.as_nanos() as f64 / iters as f64;
    let (value, unit) = if per_iter >= 1_000_000.0 {
        (per_iter / 1_000_000.0, "ms")
    } else if per_iter >= 1_000.0 {
        (per_iter / 1_000.0, "µs")
    } else {
        (per_iter, "ns")
    };
    println!(
        "  {:<55} {:>10.2} {}/iter ({} iters)",
        name, value, unit, iters
    );
}

fn main() {
    let ctx = Context::new();

    println!("=== clarirs Performance Benchmarks ===\n");

    // ========================================================================
    // 1. AST Node Creation
    // ========================================================================
    println!("--- 1. AST Node Creation ---");

    bench("bvv_creation_64bit", 100_000, || {
        let _ = black_box(ctx.bvv_prim(42u64).unwrap());
    });

    bench("bvv_creation_256bit", 50_000, || {
        let bv = BitVec::from_prim_with_size(0xDEADBEEFu64, 256).unwrap();
        let _ = black_box(ctx.bvv(bv).unwrap());
    });

    bench("bvs_creation (same name)", 100_000, || {
        let _ = black_box(ctx.bvs("x", 64).unwrap());
    });

    {
        let names: Vec<String> = (0..1000).map(|i| format!("var_{i}")).collect();
        let mut idx = 0usize;
        bench("bvs_creation_unique_names", 10_000, || {
            let name = &names[idx % names.len()];
            let _ = black_box(ctx.bvs(name, 64).unwrap());
            idx += 1;
        });
    }

    bench("boolv_creation", 100_000, || {
        let _ = black_box(ctx.boolv(true).unwrap());
    });

    // ========================================================================
    // 2. String Interning
    // ========================================================================
    println!("\n--- 2. String Interning ---");

    // Pre-intern to test cache path
    let _ = ctx.intern_string("x");
    bench("intern_same_string (cached)", 500_000, || {
        let _ = black_box(ctx.intern_string("x"));
    });

    {
        let strings: Vec<String> = (0..10_000).map(|i| format!("unique_var_{i}")).collect();
        let mut idx = 0usize;
        bench("intern_unique_strings", 10_000, || {
            let _ = black_box(ctx.intern_string(&strings[idx % strings.len()]));
            idx += 1;
        });
    }

    // ========================================================================
    // 3. Symbolic Operations
    // ========================================================================
    println!("\n--- 3. Symbolic Operations ---");

    let x64 = ctx.bvs("x", 64).unwrap();
    let y64 = ctx.bvs("y", 64).unwrap();

    bench("symbolic_add (x + y)", 50_000, || {
        let _ = black_box(ctx.add(&x64, &y64).unwrap());
    });

    bench("symbolic_bv_and (x & y)", 50_000, || {
        let _ = black_box(ctx.bv_and(&x64, &y64).unwrap());
    });

    {
        let cond = ctx.bools("c").unwrap();
        bench("symbolic_ite", 50_000, || {
            let _ = black_box(ctx.ite(&cond, &x64, &y64).unwrap());
        });
    }

    bench("symbolic_extract [31:0]", 50_000, || {
        let _ = black_box(ctx.extract(&x64, 31, 0).unwrap());
    });

    {
        let x32 = ctx.bvs("x32", 32).unwrap();
        let y32 = ctx.bvs("y32", 32).unwrap();
        bench("symbolic_concat", 50_000, || {
            let _ = black_box(ctx.concat2(&x32, &y32).unwrap());
        });
    }

    {
        let x8 = ctx.bvs("x8", 8).unwrap();
        bench("symbolic_zero_ext (8->64)", 50_000, || {
            let _ = black_box(ctx.zero_ext(&x8, 56).unwrap());
        });
    }

    bench("symbolic_comparisons (ult+slt+eq)", 20_000, || {
        let _ = black_box(ctx.ult(&x64, &y64).unwrap());
        let _ = black_box(ctx.slt(&x64, &y64).unwrap());
        let _ = black_box(ctx.eq_(&x64, &y64).unwrap());
    });

    // ========================================================================
    // 4. Concrete Arithmetic (BitVec numerics)
    // ========================================================================
    println!("\n--- 4. Concrete Arithmetic (BitVec) ---");

    {
        let a = ctx.bvv_prim(100u64).unwrap();
        let b = ctx.bvv_prim(200u64).unwrap();
        bench("concrete_add_64bit (simplifies)", 50_000, || {
            let _ = black_box(ctx.add(&a, &b).unwrap());
        });
    }

    {
        let a = ctx.bvv_prim(7u64).unwrap();
        let b = ctx.bvv_prim(6u64).unwrap();
        bench("concrete_mul_64bit (simplifies)", 50_000, || {
            let _ = black_box(ctx.mul(&a, &b).unwrap());
        });
    }

    {
        let a = ctx.bvv_prim(42u64).unwrap();
        let b = ctx.bvv_prim(6u64).unwrap();
        bench("concrete_div_64bit (simplifies)", 50_000, || {
            let _ = black_box(ctx.udiv(&a, &b).unwrap());
        });
    }

    {
        let a = BitVec::from(0xDEADBEEFu64);
        let b = BitVec::from(0xCAFEBABEu64);
        bench("bitvec_raw_add_64bit", 500_000, || {
            let _ = black_box((a.clone() + b.clone()).unwrap());
        });
    }

    {
        let a = BitVec::from(0xDEADBEEFu64);
        let b = BitVec::from(0xCAFEBABEu64);
        bench("bitvec_raw_mul_64bit (via BigUint)", 200_000, || {
            let _ = black_box((a.clone() * b.clone()).unwrap());
        });
    }

    {
        let a = BitVec::from(0xDEADBEEFu64);
        let b = BitVec::from(6u64);
        bench("bitvec_raw_div_64bit (via BigUint)", 200_000, || {
            let _ = black_box((a.clone() / b.clone()).unwrap());
        });
    }

    {
        let a = BitVec::from_prim_with_size(0xDEADBEEFu64, 256).unwrap();
        let b = BitVec::from_prim_with_size(0xCAFEBABEu64, 256).unwrap();
        bench("bitvec_raw_add_256bit", 200_000, || {
            let _ = black_box((a.clone() + b.clone()).unwrap());
        });
    }

    // ========================================================================
    // 5. Simplification
    // ========================================================================
    println!("\n--- 5. Simplification ---");

    bench("simplify_concrete_chain (10 adds)", 10_000, || {
        let mut val = ctx.bvv_prim(1u64).unwrap();
        for i in 1u64..=10 {
            val = ctx.add(&val, &ctx.bvv_prim(i).unwrap()).unwrap();
        }
        let _ = black_box(val);
    });

    {
        let all_ones = ctx.bvv(BitVec::from(u64::MAX)).unwrap();
        bench("simplify_identity (x & 0xFF..FF = x)", 50_000, || {
            let _ = black_box(ctx.bv_and(&x64, &all_ones).unwrap());
        });
    }

    {
        let zero = ctx.bvv_prim(0u64).unwrap();
        bench("simplify_identity (x | 0 = x)", 50_000, || {
            let _ = black_box(ctx.bv_or(&x64, &zero).unwrap());
        });
    }

    bench("simplify_double_not (~~x = x)", 50_000, || {
        let not_x = ctx.not(&x64).unwrap();
        let _ = black_box(ctx.not(&not_x).unwrap());
    });

    bench("simplify_bool_and_chain (10 terms)", 5_000, || {
        let vars: Vec<_> = (0..10)
            .map(|i| ctx.bools(&format!("b{i}")).unwrap())
            .collect();
        let _ = black_box(ctx.and(vars).unwrap());
    });

    // ========================================================================
    // 6. Deep Tree Construction
    // ========================================================================
    println!("\n--- 6. Deep Tree Construction ---");

    bench("deep_ite_chain (depth 50)", 1_000, || {
        let x = ctx.bvs("x", 64).unwrap();
        let mut result = x.clone();
        for i in 0..50 {
            let cond = ctx.bools(&format!("c{i}")).unwrap();
            let val = ctx.bvv_prim(i as u64).unwrap();
            result = ctx.ite(&cond, &val, &result).unwrap();
        }
        let _ = black_box(result);
    });

    bench("deep_add_chain (depth 100)", 500, || {
        let x = ctx.bvs("x", 64).unwrap();
        let mut result = x.clone();
        for i in 0u64..100 {
            let v = ctx.bvv_prim(i).unwrap();
            result = ctx.add(&result, &v).unwrap();
        }
        let _ = black_box(result);
    });

    bench("wide_bool_and (50 terms)", 2_000, || {
        let vars: Vec<_> = (0..50)
            .map(|i| ctx.bools(&format!("w{i}")).unwrap())
            .collect();
        let _ = black_box(ctx.and(vars).unwrap());
    });

    // ========================================================================
    // 7. Replace / Substitution
    // ========================================================================
    println!("\n--- 7. Replace / Substitution ---");

    {
        let y = ctx.bvs("y", 64).unwrap();
        let c42 = ctx.bvv_prim(42u64).unwrap();
        let expr = ctx.add(&x64, &c42).unwrap();
        bench("replace_leaf (x -> y in x+42)", 20_000, || {
            let _ = black_box(expr.replace(&x64, &y).unwrap());
        });
    }

    {
        let y = ctx.bvs("y", 64).unwrap();
        let c42 = ctx.bvv_prim(42u64).unwrap();
        let mut expr = x64.clone();
        for _ in 0..10 {
            expr = ctx.add(&expr, &c42).unwrap();
        }
        bench("replace_deep_tree (depth 10)", 5_000, || {
            let _ = black_box(expr.replace(&x64, &y).unwrap());
        });
    }

    // ========================================================================
    // 8. Cache Behavior
    // ========================================================================
    println!("\n--- 8. Cache Behavior ---");

    {
        // Create expression once to populate cache
        let _ = ctx.add(&x64, &y64).unwrap();
        bench("cache_hit (re-create x+y)", 100_000, || {
            let _ = black_box(ctx.add(&x64, &y64).unwrap());
        });
    }

    {
        let vals: Vec<_> = (0..1000)
            .map(|i| ctx.bvv_prim(i as u64).unwrap())
            .collect();
        let mut idx = 0usize;
        bench("cache_miss (unique x+const each time)", 10_000, || {
            let v = &vals[idx % vals.len()];
            let _ = black_box(ctx.add(&x64, v).unwrap());
            idx += 1;
        });
    }

    // ========================================================================
    // 9. Memory / Clone Overhead
    // ========================================================================
    println!("\n--- 9. Memory / Clone Overhead ---");

    bench("arc_clone (clone AstRef)", 1_000_000, || {
        let _ = black_box(x64.clone());
    });

    bench("dynast_from (BitVecAst -> DynAst)", 500_000, || {
        let _ = black_box(DynAst::from(&x64));
    });

    {
        let expr = ctx.add(&x64, &y64).unwrap();
        bench("variables() access (cached, clones BTreeSet)", 500_000, || {
            let _ = black_box(expr.variables());
        });
    }

    // ========================================================================
    // 10. Symbolic Execution Simulation
    // ========================================================================
    println!("\n--- 10. Symbolic Execution Simulation ---");

    bench("se_memory_read_pattern (16 entries)", 1_000, || {
        let addr = ctx.bvs("addr", 64).unwrap();
        let mut result = ctx.bvv_prim(0xFFu64).unwrap();
        for i in 0u64..16 {
            let cond = ctx.eq_(&addr, &ctx.bvv_prim(i).unwrap()).unwrap();
            let val = ctx.bvv_prim(i * 0x11).unwrap();
            result = ctx.ite(&cond, &val, &result).unwrap();
        }
        let _ = black_box(result);
    });

    bench("se_constraint_accumulation (20)", 1_000, || {
        let x = ctx.bvs("x", 64).unwrap();
        let mut constraints = Vec::new();
        for i in 0u64..20 {
            let bound = ctx.bvv_prim(i).unwrap();
            constraints.push(ctx.ugt(&x, &bound).unwrap());
        }
        let _ = black_box(ctx.and(constraints).unwrap());
    });

    bench("se_register_ops (typical basic block)", 2_000, || {
        let rax = ctx.bvs("rax", 64).unwrap();
        let rbx = ctx.bvs("rbx", 64).unwrap();
        let rcx = ctx.bvs("rcx", 64).unwrap();
        let rax2 = ctx.add(&rbx, &rcx).unwrap();
        let shift = ctx.bvv_prim(3u64).unwrap();
        let rax3 = ctx.shl(&rax2, &shift).unwrap();
        let mask = ctx.bvv_prim(0xFFu64).unwrap();
        let rax4 = ctx.bv_and(&rax3, &mask).unwrap();
        let _flag = ctx.eq_(&rax4, &rax).unwrap();
        let _ = black_box(_flag);
    });

    // ========================================================================
    // 11. Annotation Overhead
    // ========================================================================
    println!("\n--- 11. Annotation Overhead ---");

    bench("annotation_propagation (no annotations)", 50_000, || {
        let _ = black_box(ctx.add(&x64, &y64).unwrap());
    });

    // ========================================================================
    // 12. Hash Computation
    // ========================================================================
    println!("\n--- 12. Hash Computation ---");

    bench("hash_in_creation (BVV 64-bit)", 100_000, || {
        let bv = BitVec::from(42u64);
        let _ = black_box(ctx.bvv(bv).unwrap());
    });

    // ========================================================================
    // 13. Variables collection during construction
    // ========================================================================
    println!("\n--- 13. Variables Collection (BTreeSet union) ---");

    bench("variables_union_2_vars", 50_000, || {
        // Each add() call computes variables = union of children's vars
        let _ = black_box(ctx.add(&x64, &y64).unwrap());
    });

    {
        // Build expression with many variables
        let vars: Vec<_> = (0..10)
            .map(|i| ctx.bvs(&format!("v{i}"), 64).unwrap())
            .collect();
        let mut expr = vars[0].clone();
        for v in &vars[1..] {
            expr = ctx.add(&expr, v).unwrap();
        }
        bench("variables_10var_chain (existing)", 50_000, || {
            // Accessing cached variables
            let _ = black_box(expr.variables());
        });
    }

    // ========================================================================
    // 14. GenericCache (simplification cache) - write lock contention
    // ========================================================================
    println!("\n--- 14. Simplification Cache ---");

    bench("simplify_already_simple_bvv", 100_000, || {
        let v = ctx.bvv_prim(42u64).unwrap();
        let _ = black_box(v.simplify().unwrap());
    });

    bench("simplify_symbolic_add", 50_000, || {
        let expr = ctx.add(&x64, &y64).unwrap();
        let _ = black_box(expr.simplify().unwrap());
    });

    println!("\n=== Benchmarks Complete ===");
}
