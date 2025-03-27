use crate::{
    algorithms::simplify::{extract_bitvec_child, extract_bool_child, extract_string_child},
    prelude::*,
};

pub(crate) fn simplify_string<'c>(
    ast: &StringAst<'c>,
    children: &Vec<DynAst<'c>>,
) -> Result<StringAst<'c>, ClarirsError> {
    let ctx = ast.context();

    match &ast.op() {
        StringOp::StringS(name) => ctx.strings(name.clone()),
        StringOp::StringV(value) => ctx.stringv(value.clone()),
        StringOp::StrConcat(..) => {
            let (arc, arc1) = (
                extract_string_child!(children, 0),
                extract_string_child!(children, 1),
            );
            match (arc.op(), arc1.op()) {
                (StringOp::StringV(str1), StringOp::StringV(str2)) => {
                    let concatenated = format!("{}{}", str1, str2);
                    ctx.stringv(concatenated)
                }
                _ => ctx.strconcat(&arc, &arc1),
            }
        }
        StringOp::StrSubstr(..) => {
            let (arc, arc1, arc2) = (
                extract_string_child!(children, 0),
                extract_bitvec_child!(children, 1),
                extract_bitvec_child!(children, 2),
            );
            match (arc.op(), arc1.op(), arc2.op()) {
                (StringOp::StringV(s), BitVecOp::BVV(start_bv), BitVecOp::BVV(length_bv)) => {
                    // Convert the bitvectors to usize indices.
                    let start = start_bv.to_usize().unwrap_or(0);
                    let length = length_bv.to_usize().unwrap_or(s.chars().count());
                    let num_chars = s.chars().count();

                    // If the starting index is out-of-bound (e.g., negative index wrapped to 2^64-1),
                    // then return an empty string.
                    if start >= num_chars {
                        return ctx.stringv("".to_string());
                    }

                    // Convert character-based indices to byte-based indices.
                    let char_start = s.chars().take(start).map(|c| c.len_utf8()).sum();
                    let char_end = s.chars().take(start + length).map(|c| c.len_utf8()).sum();

                    let substring = s.get(char_start..char_end).unwrap_or("").to_string();
                    ctx.stringv(substring)
                }
                _ => ctx.strsubstr(&arc, &arc1, &arc2),
            }
        }
        StringOp::StrReplace(..) => {
            let (arc, arc1, arc2) = (
                extract_string_child!(children, 0),
                extract_string_child!(children, 1),
                extract_string_child!(children, 2),
            );
            match (arc.op(), arc1.op(), arc2.op()) {
                (
                    StringOp::StringV(initial),
                    StringOp::StringV(pattern),
                    StringOp::StringV(replacement),
                ) => {
                    // Case: Replace first occurrence of `pattern` with `replacement` in `initial` as per ClariPy DONE
                    let new_value = initial.replacen(pattern, replacement, 1);
                    // Case: Replace all occurrences of `pattern` with `replacement` in `initial` LEFT
                    // let new_value = initial.replace(pattern, replacement);
                    ctx.stringv(new_value)
                }
                _ => ctx.strreplace(&arc, &arc1, &arc2), // Fallback to symbolic StrReplace
            }
        }
        StringOp::BVToStr(..) => {
            let arc = extract_bitvec_child!(children, 0);
            match arc.op() {
                BitVecOp::BVV(value) => {
                    // Convert the BitVec value to an integer, then to a string
                    let int_value = value.to_biguint();
                    let string_value = int_value.to_string();

                    ctx.stringv(string_value)
                }
                _ => ctx.bvtostr(&arc),
            }
        }
        StringOp::If(..) => {
            let (if_, then_, else_) = (
                extract_bool_child!(children, 0),
                extract_string_child!(children, 1),
                extract_string_child!(children, 2),
            );

            // If both branches are identical, return either one
            if then_ == else_ {
                return Ok(then_.clone());
            }

            match if_.op() {
                // If the condition is a concrete boolean value, return the appropriate branch
                BooleanOp::BoolV(value) => {
                    if *value {
                        Ok(then_.clone())
                    } else {
                        Ok(else_.clone())
                    }
                }
                // If the condition has a Not at the top level, invert the branches
                BooleanOp::Not(inner) => ctx.if_(inner, &else_, &then_),
                _ => ctx.if_(&if_, &then_, &else_),
            }
        }
        StringOp::Annotated(_, annotation) => {
            let arc = extract_string_child!(children, 0);
            if annotation.eliminatable() {
                Ok(arc)
            } else if annotation.relocatable() {
                ctx.annotated(&arc, annotation.clone())
            } else {
                Ok(ast.clone())
            }
        }
    }
}
