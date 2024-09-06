use serde::Serialize;

#[repr(u8)]
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum AstKind {
    Bool,
    BitVec,
    Float,
    String,
}

impl AstKind {
    pub fn is_bool(&self) -> bool {
        matches!(self, AstKind::Bool)
    }

    pub fn is_bitvec(&self) -> bool {
        matches!(self, AstKind::BitVec)
    }

    pub fn is_float(&self) -> bool {
        matches!(self, AstKind::Float)
    }

    pub fn is_string(&self) -> bool {
        matches!(self, AstKind::String)
    }
}
