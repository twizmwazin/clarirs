use serde::Serialize;

/// Compact bit flags representing which theories an expression belongs to.
///
/// Each AST node tracks the theories present in its subtree. This is used
/// during simplification to determine which optimizations are sound. For
/// example, `a == a` can only be simplified to `true` when the subtree
/// does not involve IEEE 754 floats, since `NaN != NaN`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub struct Theories(u8);

impl Theories {
    pub const EMPTY: Self = Self(0);
    pub const BOOLEAN: Self = Self(1 << 0);
    pub const BITVEC: Self = Self(1 << 1);
    pub const FLOAT: Self = Self(1 << 2);
    pub const STRING: Self = Self(1 << 3);

    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

impl std::ops::BitOr for Theories {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

impl std::ops::BitOrAssign for Theories {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}
