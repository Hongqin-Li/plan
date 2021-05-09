//! Common error types for kernel development.
use core::alloc::AllocError;

use alloc::collections::TryReserveError;

/// Kernel errors.
#[derive(Debug)]
pub enum Error {
    /// When global allocator returns zero.
    OutOfMemory,
    /// When access is forbidden.
    Forbidden,
    /// When something not found.
    NotFound,
    /// Cannot or will not process the request due to something that is perceived
    /// to be a client error.
    BadRequest,
    /// When operation timeout.
    Timeout,
    /// When something already exists.
    Conflict,
    /// Access to the target resource that is no longer available.
    /// For example, when accessing a removed sd card.
    Gone,
    /// When hardware error.
    InternalError,
    /// When disk used out.
    InsufficientStorage,
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
