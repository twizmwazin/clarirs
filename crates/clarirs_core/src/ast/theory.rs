use bitflags::bitflags;

bitflags! {
    /// Compact bit flags representing which theories an expression belongs to.
    ///
    /// Each AST node tracks the theories present in its subtree. This is used
    /// during simplification to determine which optimizations are sound. For
    /// example, `a == a` can only be simplified to `true` when the subtree
    /// does not involve IEEE 754 floats, since `NaN != NaN`.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub struct Theories: u8 {
        const BOOLEAN = 1 << 0;
        const BITVEC  = 1 << 1;
        const FLOAT   = 1 << 2;
        const STRING  = 1 << 3;
    }
}

impl serde::Serialize for Theories {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.bits().serialize(serializer)
    }
}
