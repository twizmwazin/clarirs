use crate::prelude::*;

pub trait ToOpString {
    fn to_opstring(&self) -> String;
}

impl ToOpString for AstRef<'static> {
    fn to_opstring(&self) -> String {
        match self.op() {
            // Boolean
            AstOp::BoolS(..) => "BoolS".to_string(),
            AstOp::BoolV(..) => "BoolV".to_string(),

            // Cross-sort ops need context to determine the Python op name
            AstOp::Not(..) => {
                if self.op().base_theories() == Theories::BOOLEAN {
                    "Not".to_string()
                } else {
                    "__neg__".to_string()
                }
            }
            AstOp::And(..) => {
                if self.op().base_theories() == Theories::BOOLEAN {
                    "And".to_string()
                } else {
                    "__and__".to_string()
                }
            }
            AstOp::Or(..) => {
                if self.op().base_theories() == Theories::BOOLEAN {
                    "Or".to_string()
                } else {
                    "__or__".to_string()
                }
            }
            AstOp::Xor(..) => {
                if self.op().base_theories() == Theories::BOOLEAN {
                    "Xor".to_string()
                } else {
                    "__xor__".to_string()
                }
            }
            AstOp::Eq(..) => "__eq__".to_string(),
            AstOp::Neq(..) => "__ne__".to_string(),
            AstOp::If(..) => "If".to_string(),

            // BV
            AstOp::BVS(..) => "BVS".to_string(),
            AstOp::BVV(..) => "BVV".to_string(),
            AstOp::Neg(..) => "__neg__".to_string(),
            AstOp::Add(..) => "__add__".to_string(),
            AstOp::Sub(..) => "__sub__".to_string(),
            AstOp::Mul(..) => "__mul__".to_string(),
            AstOp::UDiv(..) => "__floordiv__".to_string(),
            AstOp::SDiv(..) => "SDiv".to_string(),
            AstOp::URem(..) => "__mod__".to_string(),
            AstOp::SRem(..) => "SMod".to_string(),
            AstOp::ShL(..) => "__lshift__".to_string(),
            AstOp::LShR(..) => "LShR".to_string(),
            AstOp::AShR(..) => "__rshift__".to_string(),
            AstOp::RotateLeft(..) => "RotateLeft".to_string(),
            AstOp::RotateRight(..) => "RotateRight".to_string(),
            AstOp::ZeroExt(..) => "ZeroExt".to_string(),
            AstOp::SignExt(..) => "SignExt".to_string(),
            AstOp::Extract(..) => "Extract".to_string(),
            AstOp::Concat(..) => "Concat".to_string(),
            AstOp::ByteReverse(..) => "Reverse".to_string(),
            AstOp::ULT(..) => "ULT".to_string(),
            AstOp::ULE(..) => "ULE".to_string(),
            AstOp::UGT(..) => "UGT".to_string(),
            AstOp::UGE(..) => "UGE".to_string(),
            AstOp::SLT(..) => "SLT".to_string(),
            AstOp::SLE(..) => "SLE".to_string(),
            AstOp::SGT(..) => "SGT".to_string(),
            AstOp::SGE(..) => "SGE".to_string(),
            AstOp::FpToIEEEBV(..) => "fpToIEEEBV".to_string(),
            AstOp::FpToUBV(..) => "fpToUBV".to_string(),
            AstOp::FpToSBV(..) => "fpToSBV".to_string(),
            AstOp::StrLen(..) => "StrLen".to_string(),
            AstOp::StrIndexOf(..) => "StrIndexOf".to_string(),
            AstOp::StrToBV(..) => "StrToBV".to_string(),
            AstOp::Union(..) => "Union".to_string(),
            AstOp::Intersection(..) => "Intersection".to_string(),
            AstOp::Widen(..) => "Widen".to_string(),

            // Float
            AstOp::FPS(..) => "FPS".to_string(),
            AstOp::FPV(..) => "FPV".to_string(),
            AstOp::FpNeg(..) => "fpNeg".to_string(),
            AstOp::FpAbs(..) => "fpAbs".to_string(),
            AstOp::FpAdd(..) => "fpAdd".to_string(),
            AstOp::FpSub(..) => "fpSub".to_string(),
            AstOp::FpMul(..) => "fpMul".to_string(),
            AstOp::FpDiv(..) => "fpDiv".to_string(),
            AstOp::FpSqrt(..) => "fpSqrt".to_string(),
            AstOp::FpToFp(..) => "fpToFp".to_string(),
            AstOp::FpFP(..) => "fpFP".to_string(),
            AstOp::BvToFp(..) => "bvToFP".to_string(),
            AstOp::BvToFpSigned(..) => "fpToFPSigned".to_string(),
            AstOp::BvToFpUnsigned(..) => "fpToFPUnsigned".to_string(),
            AstOp::FpLt(..) => "fpLT".to_string(),
            AstOp::FpLeq(..) => "fpLEQ".to_string(),
            AstOp::FpGt(..) => "fpGT".to_string(),
            AstOp::FpGeq(..) => "fpGEQ".to_string(),
            AstOp::FpIsNan(..) => "fpIsNan".to_string(),
            AstOp::FpIsInf(..) => "fpIsInf".to_string(),

            // String
            AstOp::StringS(..) => "StringS".to_string(),
            AstOp::StringV(..) => "StringV".to_string(),
            AstOp::StrConcat(..) => "StrConcat".to_string(),
            AstOp::StrSubstr(..) => "StrSubstr".to_string(),
            AstOp::StrReplace(..) => "StrReplace".to_string(),
            AstOp::BVToStr(..) => "IntToStr".to_string(),
            AstOp::StrContains(..) => "StrContains".to_string(),
            AstOp::StrPrefixOf(..) => "StrPrefixOf".to_string(),
            AstOp::StrSuffixOf(..) => "StrSuffixOf".to_string(),
            AstOp::StrIsDigit(..) => "StrIsDigit".to_string(),
        }
    }
}
