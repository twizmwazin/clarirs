use crate::prelude::*;

pub trait ToOpString {
    fn to_opstring(&self) -> String;
}

impl ToOpString for BoolAst<'static> {
    fn to_opstring(&self) -> String {
        match self.op() {
            BooleanOp::BoolS(..) => "BoolS".to_string(),
            BooleanOp::BoolV(..) => "BoolV".to_string(),
            BooleanOp::Not(..) => "Not".to_string(),
            BooleanOp::And(..) => "And".to_string(),
            BooleanOp::Or(..) => "Or".to_string(),
            BooleanOp::Xor(..) => "Xor".to_string(),
            BooleanOp::BoolEq(..) => "__eq__".to_string(),
            BooleanOp::BoolNeq(..) => "__ne__".to_string(),
            BooleanOp::Eq(..) => "__eq__".to_string(),
            BooleanOp::Neq(..) => "__ne__".to_string(),
            BooleanOp::ULT(..) => "ULT".to_string(),
            BooleanOp::ULE(..) => "ULE".to_string(),
            BooleanOp::UGT(..) => "UGT".to_string(),
            BooleanOp::UGE(..) => "UGE".to_string(),
            BooleanOp::SLT(..) => "SLT".to_string(),
            BooleanOp::SLE(..) => "SLE".to_string(),
            BooleanOp::SGT(..) => "SGT".to_string(),
            BooleanOp::SGE(..) => "SGE".to_string(),
            BooleanOp::FpEq(..) => "fpEQ".to_string(),
            BooleanOp::FpNeq(..) => "fpNEQ".to_string(),
            BooleanOp::FpLt(..) => "fpLT".to_string(),
            BooleanOp::FpLeq(..) => "fpLEQ".to_string(),
            BooleanOp::FpGt(..) => "fpGT".to_string(),
            BooleanOp::FpGeq(..) => "fpGEQ".to_string(),
            BooleanOp::FpIsNan(..) => "fpIsNan".to_string(),
            BooleanOp::FpIsInf(..) => "fpIsInf".to_string(),
            BooleanOp::StrContains(..) => "StrContains".to_string(),
            BooleanOp::StrPrefixOf(..) => "StrPrefixOf".to_string(),
            BooleanOp::StrSuffixOf(..) => "StrSuffixOf".to_string(),
            BooleanOp::StrIsDigit(..) => "StrIsDigit".to_string(),
            BooleanOp::StrEq(..) => "__eq__".to_string(),
            BooleanOp::StrNeq(..) => "__ne__".to_string(),
            BooleanOp::ITE(..) => "If".to_string(),
        }
    }
}

impl ToOpString for BitVecAst<'static> {
    fn to_opstring(&self) -> String {
        match self.op() {
            BitVecOp::BVS(..) => "BVS".to_string(),
            BitVecOp::BVV(..) => "BVV".to_string(),
            BitVecOp::Not(..) => "__neg__".to_string(),
            BitVecOp::And(..) => "__and__".to_string(),
            BitVecOp::Or(..) => "__or__".to_string(),
            BitVecOp::Xor(..) => "__xor__".to_string(),
            BitVecOp::Neg(..) => "__neg__".to_string(),
            BitVecOp::Add(..) => "__add__".to_string(),
            BitVecOp::Sub(..) => "__sub__".to_string(),
            BitVecOp::Mul(..) => "__mul__".to_string(),
            BitVecOp::UDiv(..) => "__floordiv__".to_string(),
            BitVecOp::SDiv(..) => "SDiv".to_string(),
            BitVecOp::URem(..) => "__mod__".to_string(),
            BitVecOp::SRem(..) => "SMod".to_string(),
            BitVecOp::ShL(..) => "__lshift__".to_string(),
            BitVecOp::LShR(..) => "LShR".to_string(),
            BitVecOp::AShR(..) => "__rshift__".to_string(),
            BitVecOp::RotateLeft(..) => "RotateLeft".to_string(),
            BitVecOp::RotateRight(..) => "RotateRight".to_string(),
            BitVecOp::ZeroExt(..) => "ZeroExt".to_string(),
            BitVecOp::SignExt(..) => "SignExt".to_string(),
            BitVecOp::Extract(..) => "Extract".to_string(),
            BitVecOp::Concat(..) => "Concat".to_string(),
            BitVecOp::ByteReverse(..) => "Reverse".to_string(),
            BitVecOp::FpToIEEEBV(..) => "fpToIEEEBV".to_string(),
            BitVecOp::FpToUBV(..) => "fpToUBV".to_string(),
            BitVecOp::FpToSBV(..) => "fpToSBV".to_string(),
            BitVecOp::StrLen(..) => "StrLen".to_string(),
            BitVecOp::StrIndexOf(..) => "StrIndexOf".to_string(),
            BitVecOp::StrToBV(..) => "StrToBV".to_string(),
            BitVecOp::ITE(..) => "If".to_string(),
            BitVecOp::Union(..) => "Union".to_string(),
            BitVecOp::Intersection(..) => "Intersection".to_string(),
            BitVecOp::Widen(..) => "Widen".to_string(),
        }
    }
}

impl ToOpString for FloatAst<'static> {
    fn to_opstring(&self) -> String {
        match self.op() {
            FloatOp::FPS(..) => "FPS".to_string(),
            FloatOp::FPV(..) => "FPV".to_string(),
            FloatOp::FpNeg(..) => "fpNeg".to_string(),
            FloatOp::FpAbs(..) => "fpAbs".to_string(),
            FloatOp::FpAdd(..) => "fpAdd".to_string(),
            FloatOp::FpSub(..) => "fpSub".to_string(),
            FloatOp::FpMul(..) => "fpMul".to_string(),
            FloatOp::FpDiv(..) => "fpDiv".to_string(),
            FloatOp::FpSqrt(..) => "fpSqrt".to_string(),
            FloatOp::FpToFp(..) => "fpToFp".to_string(),
            FloatOp::FpFP(..) => "fpFP".to_string(),
            FloatOp::BvToFp(..) => "bvToFP".to_string(),
            FloatOp::BvToFpSigned(..) => "fpToFPSigned".to_string(),
            FloatOp::BvToFpUnsigned(..) => "fpToFPUnsigned".to_string(),
            FloatOp::ITE(..) => "If".to_string(),
        }
    }
}

impl ToOpString for StringAst<'static> {
    fn to_opstring(&self) -> String {
        match self.op() {
            StringOp::StringS(..) => "StringS".to_string(),
            StringOp::StringV(..) => "StringV".to_string(),
            StringOp::StrConcat(..) => "StrConcat".to_string(),
            StringOp::StrSubstr(..) => "StrSubstr".to_string(),
            StringOp::StrReplace(..) => "StrReplace".to_string(),
            StringOp::BVToStr(..) => "IntToStr".to_string(),
            StringOp::ITE(..) => "If".to_string(),
        }
    }
}

impl ToOpString for DynAst<'static> {
    fn to_opstring(&self) -> String {
        match self {
            DynAst::Boolean(b) => b.to_opstring(),
            DynAst::BitVec(b) => b.to_opstring(),
            DynAst::Float(b) => b.to_opstring(),
            DynAst::String(b) => b.to_opstring(),
        }
    }
}
