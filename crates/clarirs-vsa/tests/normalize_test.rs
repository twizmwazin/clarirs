use clarirs_core::ast::annotation::{Annotation, AnnotationType};
use clarirs_core::prelude::*;
use clarirs_vsa::normalize::Normalize;

#[test]
fn test_normalize_bvv() {
    let ctx = Context::new();

    // Create a simple BVV (concrete bitvector value)
    let bv = ctx.bvv_prim(42u64).unwrap();

    // Normalize it
    let normalized = bv.normalize().unwrap();

    // Check that it was converted to an SI
    match normalized.op() {
        BitVecOp::SI(size, stride, lower, upper) => {
            assert_eq!(*size, 64); // bvv_prim creates a 64-bit bitvector by default
            assert_eq!(*stride, 1u32.into());
            assert_eq!(*lower, 42u64.into());
            assert_eq!(*upper, 42u64.into());
        }
        _ => panic!("Expected SI, got {:?}", normalized.op()),
    }
}

#[test]
fn test_normalize_bvs_error() {
    let ctx = Context::new();

    // Create a BVS (symbolic bitvector) without SI annotation
    let bvs = ctx.bvs("x", 32).unwrap();

    // Normalization should fail because BVS needs SI annotation
    let result = bvs.normalize();
    assert!(result.is_err());

    if let Err(ClarirsError::UnsupportedOperation(msg)) = result {
        assert!(msg.contains("VSA expects BVS to have an SI annotation"));
    } else {
        panic!("Expected UnsupportedOperation error");
    }
}

#[test]
fn test_normalize_si_annotation() {
    let ctx = Context::new();

    // Create a BVS with SI annotation
    let bvs = ctx.bvs("x", 32).unwrap();

    // Create an SI annotation
    let annotation = Annotation::new(
        AnnotationType::StridedInterval {
            stride: 2u32.into(),
            lower_bound: 10u32.into(),
            upper_bound: 20u32.into(),
        },
        true,  // eliminatable
        false, // relocatable
    );

    // Annotate the BVS with SI
    let annotated = ctx.annotated(&bvs, annotation).unwrap();

    // Normalize it
    let normalized = annotated.normalize().unwrap();

    // Check that it was converted to an SI
    match normalized.op() {
        BitVecOp::SI(size, stride, lower, upper) => {
            assert_eq!(*size, 32);
            assert_eq!(*stride, 2u32.into());
            assert_eq!(*lower, 10u32.into());
            assert_eq!(*upper, 20u32.into());
        }
        _ => panic!("Expected SI, got {:?}", normalized.op()),
    }
}

#[test]
fn test_normalize_binary_operations() {
    let ctx = Context::new();

    // Create two BVVs
    let bv1 = ctx.bvv_prim(10u64).unwrap();
    let bv2 = ctx.bvv_prim(20u64).unwrap();

    // Create binary operations
    let add = ctx.add(&bv1, &bv2).unwrap();
    let and = ctx.and(&bv1, &bv2).unwrap();
    let or = ctx.or(&bv1, &bv2).unwrap();

    // Normalize them
    let normalized_add = add.normalize().unwrap();
    let normalized_and = and.normalize().unwrap();
    let normalized_or = or.normalize().unwrap();

    // Check that the operations were preserved and operands were normalized
    match normalized_add.op() {
        BitVecOp::Add(lhs, rhs) => {
            // Check that operands were normalized to SI
            assert!(matches!(lhs.op(), BitVecOp::SI(..)));
            assert!(matches!(rhs.op(), BitVecOp::SI(..)));
        }
        _ => panic!("Expected Add operation"),
    }

    match normalized_and.op() {
        BitVecOp::And(lhs, rhs) => {
            // Check that operands were normalized to SI
            assert!(matches!(lhs.op(), BitVecOp::SI(..)));
            assert!(matches!(rhs.op(), BitVecOp::SI(..)));
        }
        _ => panic!("Expected And operation"),
    }

    match normalized_or.op() {
        BitVecOp::Or(lhs, rhs) => {
            // Check that operands were normalized to SI
            assert!(matches!(lhs.op(), BitVecOp::SI(..)));
            assert!(matches!(rhs.op(), BitVecOp::SI(..)));
        }
        _ => panic!("Expected Or operation"),
    }
}

#[test]
fn test_normalize_unary_operations() {
    let ctx = Context::new();

    // Create a BVV
    let bv = ctx.bvv_prim(42u64).unwrap();

    // Create unary operations
    let not = ctx.not(&bv).unwrap();
    let neg = ctx.neg(&bv).unwrap();

    // Normalize them
    let normalized_not = not.normalize().unwrap();
    let normalized_neg = neg.normalize().unwrap();

    // Check that the operations were preserved and operands were normalized
    match normalized_not.op() {
        BitVecOp::Not(operand) => {
            // Check that operand was normalized to SI
            assert!(matches!(operand.op(), BitVecOp::SI(..)));
        }
        _ => panic!("Expected Not operation"),
    }

    match normalized_neg.op() {
        BitVecOp::Neg(operand) => {
            // Check that operand was normalized to SI
            assert!(matches!(operand.op(), BitVecOp::SI(..)));
        }
        _ => panic!("Expected Neg operation"),
    }
}

#[test]
fn test_normalize_nested_operations() {
    let ctx = Context::new();

    // Create BVVs
    let bv1 = ctx.bvv_prim(10u64).unwrap();
    let bv2 = ctx.bvv_prim(20u64).unwrap();
    let bv3 = ctx.bvv_prim(30u64).unwrap();

    // Create nested operations: (bv1 + bv2) & bv3
    let add = ctx.add(&bv1, &bv2).unwrap();
    let and = ctx.and(&add, &bv3).unwrap();

    // Normalize the nested expression
    let normalized = and.normalize().unwrap();

    // Check that the operations were preserved and operands were normalized
    match normalized.op() {
        BitVecOp::And(lhs, rhs) => {
            // Check that rhs was normalized to SI
            assert!(matches!(rhs.op(), BitVecOp::SI(..)));

            // Check that lhs is an Add operation with normalized operands
            match lhs.op() {
                BitVecOp::Add(add_lhs, add_rhs) => {
                    assert!(matches!(add_lhs.op(), BitVecOp::SI(..)));
                    assert!(matches!(add_rhs.op(), BitVecOp::SI(..)));
                }
                _ => panic!("Expected Add operation"),
            }
        }
        _ => panic!("Expected And operation"),
    }
}

#[test]
fn test_normalize_if_operation() {
    let ctx = Context::new();

    // Create a boolean condition and two BVVs
    let cond = ctx.boolv(true).unwrap();
    let then_branch = ctx.bvv_prim(10u64).unwrap();
    let else_branch = ctx.bvv_prim(20u64).unwrap();

    // Create an If operation
    let if_op = ctx.if_(&cond, &then_branch, &else_branch).unwrap();

    // Normalize it
    let normalized = if_op.normalize().unwrap();

    // Check that the operation was preserved and operands were normalized
    match normalized.op() {
        BitVecOp::If(norm_cond, norm_then, norm_else) => {
            // Check that condition is preserved (BoolV is kept as is)
            assert!(matches!(norm_cond.op(), BooleanOp::BoolV(true)));

            // Check that branches were normalized to SI
            assert!(matches!(norm_then.op(), BitVecOp::SI(..)));
            assert!(matches!(norm_else.op(), BitVecOp::SI(..)));
        }
        _ => panic!("Expected If operation"),
    }
}

#[test]
fn test_normalize_floating_point_error() {
    let ctx = Context::new();

    // Create a floating point value
    let fp = ctx.fpv_from_f64(std::f64::consts::PI).unwrap();

    // Try to convert it to a bitvector
    let fp_to_bv = ctx.fp_to_ieeebv(&fp).unwrap();

    // Normalization should fail because floating point operations are not supported
    let result = fp_to_bv.normalize();
    assert!(result.is_err());

    if let Err(ClarirsError::UnsupportedOperation(msg)) = result {
        assert!(msg.contains("Floating point operations are not supported in VSA"));
    } else {
        panic!("Expected UnsupportedOperation error");
    }
}

#[test]
fn test_normalize_string_error() {
    let ctx = Context::new();

    // Create a string value
    let str = ctx.stringv("hello").unwrap();

    // Try to get its length as a bitvector
    let str_len = ctx.strlen(&str).unwrap();

    // Normalization should fail because string operations are not supported
    let result = str_len.normalize();
    assert!(result.is_err());

    if let Err(ClarirsError::UnsupportedOperation(msg)) = result {
        assert!(msg.contains("String operations are not supported in VSA"));
    } else {
        panic!("Expected UnsupportedOperation error");
    }
}

#[test]
fn test_normalize_si_preserved() {
    let ctx = Context::new();

    // Create an SI directly
    let si = ctx.si(32, 2u32.into(), 10u32.into(), 20u32.into()).unwrap();

    // Normalize it
    let normalized = si.normalize().unwrap();

    // Check that the SI is preserved as is
    match normalized.op() {
        BitVecOp::SI(size, stride, lower, upper) => {
            assert_eq!(*size, 32);
            assert_eq!(*stride, 2u32.into());
            assert_eq!(*lower, 10u32.into());
            assert_eq!(*upper, 20u32.into());
        }
        _ => panic!("Expected SI, got {:?}", normalized.op()),
    }

    // Check that it's the same object (cloned)
    assert_eq!(si, normalized);
}

#[test]
fn test_normalize_bool_operations() {
    let ctx = Context::new();

    // Create boolean values
    let bool1 = ctx.boolv(true).unwrap();
    let bool2 = ctx.boolv(false).unwrap();

    // Create boolean operations
    let and = ctx.and(&bool1, &bool2).unwrap();
    let or = ctx.or(&bool1, &bool2).unwrap();
    let not = ctx.not(&bool1).unwrap();

    // Normalize them
    let normalized_and = and.normalize().unwrap();
    let normalized_or = or.normalize().unwrap();
    let normalized_not = not.normalize().unwrap();

    // Check that the operations were preserved
    assert!(matches!(normalized_and.op(), BooleanOp::And(..)));
    assert!(matches!(normalized_or.op(), BooleanOp::Or(..)));
    assert!(matches!(normalized_not.op(), BooleanOp::Not(..)));

    // Check that the operands were preserved (BoolV is kept as is)
    match normalized_and.op() {
        BooleanOp::And(lhs, rhs) => {
            assert!(matches!(lhs.op(), BooleanOp::BoolV(true)));
            assert!(matches!(rhs.op(), BooleanOp::BoolV(false)));
        }
        _ => panic!("Expected And operation"),
    }
}

#[test]
fn test_normalize_bool_comparison() {
    let ctx = Context::new();

    // Create BVVs
    let bv1 = ctx.bvv_prim(10u64).unwrap();
    let bv2 = ctx.bvv_prim(20u64).unwrap();

    // Create comparison operations
    let eq = ctx.eq_(&bv1, &bv2).unwrap();
    let ult = ctx.ult(&bv1, &bv2).unwrap();

    // Normalize them
    let normalized_eq = eq.normalize().unwrap();
    let normalized_ult = ult.normalize().unwrap();

    // Check that the operations were preserved and operands were normalized
    match normalized_eq.op() {
        BooleanOp::Eq(lhs, rhs) => {
            // Check that operands were normalized to SI
            assert!(matches!(lhs.op(), BitVecOp::SI(..)));
            assert!(matches!(rhs.op(), BitVecOp::SI(..)));
        }
        _ => panic!("Expected Eq operation"),
    }

    match normalized_ult.op() {
        BooleanOp::ULT(lhs, rhs) => {
            // Check that operands were normalized to SI
            assert!(matches!(lhs.op(), BitVecOp::SI(..)));
            assert!(matches!(rhs.op(), BitVecOp::SI(..)));
        }
        _ => panic!("Expected ULT operation"),
    }
}

#[test]
fn test_normalize_bool_floating_point_error() {
    let ctx = Context::new();

    // Create floating point values
    let fp1 = ctx.fpv_from_f64(std::f64::consts::PI).unwrap();
    let fp2 = ctx.fpv_from_f64(std::f64::consts::E).unwrap();

    // Create a floating point comparison
    let fp_eq = ctx.fp_eq(&fp1, &fp2).unwrap();

    // Normalization should fail because floating point operations are not supported
    let result = fp_eq.normalize();
    assert!(result.is_err());

    if let Err(ClarirsError::UnsupportedOperation(msg)) = result {
        assert!(msg.contains("Floating point operations are not supported in VSA"));
    } else {
        panic!("Expected UnsupportedOperation error");
    }
}

#[test]
fn test_normalize_bool_string_error() {
    let ctx = Context::new();

    // Create string values
    let str1 = ctx.stringv("hello").unwrap();
    let str2 = ctx.stringv("world").unwrap();

    // Create a string comparison
    let str_eq = ctx.streq(&str1, &str2).unwrap();

    // Normalization should fail because string operations are not supported
    let result = str_eq.normalize();
    assert!(result.is_err());

    if let Err(ClarirsError::UnsupportedOperation(msg)) = result {
        assert!(msg.contains("String operations are not supported in VSA"));
    } else {
        panic!("Expected UnsupportedOperation error");
    }
}

#[test]
fn test_normalize_bool_symbolic() {
    let ctx = Context::new();

    // Create a symbolic boolean
    let bools = ctx.bools("b").unwrap();

    // Normalize it
    let normalized = bools.normalize().unwrap();

    // Check that it's preserved as is
    assert!(matches!(normalized.op(), BooleanOp::BoolS(..)));

    // Check that it's the same object (cloned)
    assert_eq!(bools, normalized);
}

#[test]
fn test_normalize_bool_annotated() {
    let ctx = Context::new();

    // Create a boolean value
    let bool_val = ctx.boolv(true).unwrap();

    // Create a custom annotation
    let annotation = Annotation::new(
        AnnotationType::Unknown {
            name: "TestAnnotation".to_string(),
            value: vec![1, 2, 3],
        },
        true,  // eliminatable
        false, // relocatable
    );

    // Annotate the boolean
    let annotated = ctx.annotated(&bool_val, annotation.clone()).unwrap();

    // Normalize it
    let normalized = annotated.normalize().unwrap();

    // Check that the annotation is preserved
    match normalized.op() {
        BooleanOp::Annotated(inner, anno) => {
            // Check that inner value was preserved
            assert!(matches!(inner.op(), BooleanOp::BoolV(true)));

            // Check that annotation was preserved
            assert_eq!(anno, &annotation);
        }
        _ => panic!("Expected Annotated operation"),
    }
}
