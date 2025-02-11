use clarirs_core::error::ClarirsError;

pub(crate) trait AstExt<'ctx>: z3::ast::Ast<'ctx> {
    fn arg_bool(&'ctx self, idx: usize) -> Result<z3::ast::Bool<'ctx>, ClarirsError> {
        self.nth_child(idx)
            .ok_or(ClarirsError::UnknownError(
                "Failed to get nth child".to_string(),
            ))
            .and_then(|child| {
                child.as_bool().ok_or(ClarirsError::UnknownError(
                    "Failed to get as bool".to_string(),
                ))
            })
    }

    fn arg_bv(&'ctx self, idx: usize) -> Result<z3::ast::BV<'ctx>, ClarirsError> {
        self.nth_child(idx)
            .ok_or(ClarirsError::UnknownError(
                "Failed to get nth child".to_string(),
            ))
            .and_then(|child| {
                child.as_bv().ok_or(ClarirsError::UnknownError(
                    "Failed to get as bv".to_string(),
                ))
            })
    }

    fn arg_float(&'ctx self, idx: usize) -> Result<z3::ast::Float<'ctx>, ClarirsError> {
        self.nth_child(idx)
            .ok_or(ClarirsError::UnknownError(
                "Failed to get nth child".to_string(),
            ))
            .and_then(|child| {
                child.as_float().ok_or(ClarirsError::UnknownError(
                    "Failed to get as float".to_string(),
                ))
            })
    }

    fn arg_string(&'ctx self, idx: usize) -> Result<z3::ast::String<'ctx>, ClarirsError> {
        self.nth_child(idx)
            .ok_or(ClarirsError::UnknownError(
                "Failed to get nth child".to_string(),
            ))
            .and_then(|child| {
                child.as_string().ok_or(ClarirsError::UnknownError(
                    "Failed to get as string".to_string(),
                ))
            })
    }
}

impl<'ctx, T: z3::ast::Ast<'ctx>> AstExt<'ctx> for T {}
