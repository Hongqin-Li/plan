//! Common error types for kernel development.
use core::alloc::AllocError;

use alloc::collections::TryReserveError;

/// Kernel errors.
#[derive(Debug)]
pub enum Error {
    /// When global allocator returns zero.
    OutOfMemory,
    /// When something not found.
    NotFound,
    /// When arguments are invalid.
    BadRequest,
    /// When operation timeout.
    Timeout,
    /// When hardware error.
    InternalError,
    /// When something already exists.
    Conflict,
    /// When feature not yet implemented.
    NotImplemented,
}

/// Sugar of error.
pub type Result<T> = core::result::Result<T, Error>;

impl From<AllocError> for Error {
    fn from(x: AllocError) -> Self {
        Error::OutOfMemory
    }
}
impl From<TryReserveError> for Error {
    fn from(x: TryReserveError) -> Self {
        Error::OutOfMemory
    }
}

impl From<hashbrown::TryReserveError> for Error {
    fn from(x: hashbrown::TryReserveError) -> Self {
        Error::OutOfMemory
    }
}
