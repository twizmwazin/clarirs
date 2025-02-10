use crate::{algorithms::simplify::simplify, prelude::*};

#[allow(unused_variables)]
impl<'c> Simplify<'c> for StringAst<'c> {
    fn simplify(&self) -> Result<Self, ClarirsError> {
        let ctx = self.context();
        let hash = self.hash();

        ctx.simplification_cache
            .get_or_insert_with_string(hash, || {
                match &self.op() {
                    StringOp::StringS(name) => ctx.strings(name.clone()),
                    StringOp::StringV(value) => ctx.stringv(value.clone()),
                    StringOp::StrConcat(arc, arc1) => {
                        simplify!(arc, arc1);
                        match (arc.op(), arc1.op()) {
                            (StringOp::StringV(str1), StringOp::StringV(str2)) => {
                                let concatenated = format!("{}{}", str1, str2);
                                ctx.stringv(concatenated)
                            }
                            _ => ctx.strconcat(&arc, &arc1),
                        }
                    }
                    StringOp::StrSubstr(arc, arc1, arc2) => {
                        simplify!(arc, arc1, arc2);
                        match (arc.op(), arc1.op(), arc2.op()) {
                            (
                                StringOp::StringV(str),
                                BitVecOp::BVV(start),
                                BitVecOp::BVV(length),
                            ) => {
                                // Convert start and length to isize, then handle them as usize if they are non-negative
                                let start = start.to_usize().unwrap_or(0).max(0);
                                let length = length.to_usize().unwrap_or(str.len()).max(0);
                                let end = start.saturating_add(length).min(str.len());

                                // Extract the substring safely within bounds
                                let substring = str.get(start..end).unwrap_or("").to_string();
                                ctx.stringv(substring)
                            }
                            _ => ctx.strsubstr(&arc, &arc1, &arc2),
                        }
                    }
                    StringOp::StrReplace(arc, arc1, arc2) => {
                        simplify!(arc, arc1, arc2); // Simplify all arguments
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
                    StringOp::BVToStr(arc) => {
                        simplify!(arc);

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
                    StringOp::If(arc, arc1, arc2) => todo!("string if simplification"),
                    StringOp::Annotated(arc, annotation) => {
                        todo!("string annotation simplification")
                    }
                }
            })
    }
}
