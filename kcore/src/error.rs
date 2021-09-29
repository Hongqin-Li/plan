//! Common error types for kernel development.
use alloc::collections::TryReserveError;
use alloc::string::FromUtf8Error;
use core::alloc::AllocError;
use core::str::Utf8Error;

/// Kernel errors.
#[derive(Debug, Copy, Clone)]
pub enum Error {
    /// When global allocator returns zero.
    OutOfMemory(&'static str),
    /// When access is forbidden.
    Forbidden(&'static str),
    /// When something not found.
    NotFound(&'static str),
    /// Cannot or will not process the request due to something that is perceived
    /// to be a client error.
    BadRequest(&'static str),
    /// When operation timeout.
    Timeout(&'static str),
    /// When something already exists.
    Conflict(&'static str),
    /// Access to the target resource that is no longer available.
    /// For example, when accessing a removed sd card.
    Gone(&'static str),
    /// When hardware error.
    InternalError(&'static str),
    /// When disk used out.
    InsufficientStorage(&'static str),
    /// When feature not yet implemented.
    NotImplemented(&'static str),
    /// When page fault triggered at invalid virtual address.
    SegmentFault,
}

/// Sugar of error.
pub type Result<T> = core::result::Result<T, Error>;

impl From<AllocError> for Error {
    fn from(_: AllocError) -> Self {
        Error::OutOfMemory("alloc error")
    }
}

impl From<TryReserveError> for Error {
    fn from(_: TryReserveError) -> Self {
        Error::OutOfMemory("try reserve error")
    }
}

impl From<hashbrown::TryReserveError> for Error {
    fn from(_: hashbrown::TryReserveError) -> Self {
        Error::OutOfMemory("try reserve error")
    }
}

impl From<FromUtf8Error> for Error {
    fn from(_: FromUtf8Error) -> Self {
        Error::BadRequest("from utf8 error")
    }
}

impl From<Utf8Error> for Error {
    fn from(_: Utf8Error) -> Self {
        Error::BadRequest("utf8 error")
    }
}
