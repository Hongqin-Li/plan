//! Temporal quantification.
//!
//! Example:
//!
//! ```
//! use ksched::time::Duration;
//!
//! let five_seconds = Duration::new(5, 0);
//! // both declarations are equivalent
//! assert_eq!(Duration::new(5, 0), Duration::from_secs(5));
//! ```

use core::fmt;
use core::ops::{Add, AddAssign, Sub, SubAssign};

pub use core::time::Duration;

use crate::sync::Spinlock;

static T: Spinlock<Option<fn() -> Duration>> = Spinlock::new(None);

/// Set the instant timestamp generator, which must always returns non-decreasing nano seconds.
/// The absolute value of such timestamp is meaningless.
pub fn set_timer(fp: fn() -> Duration) {
    let mut t = T.lock();
    *t = Some(fp);
}

/// A measurement of a monotonically nondecreasing clock.
/// Opaque and useful only with `Duration`.
///
/// Instants are always guaranteed to be no less than any previously measured
/// instant when created, and are often useful for tasks such as measuring
/// benchmarks or timing how long an operation takes.
///
/// Note, however, that instants are not guaranteed to be **steady**. In other
/// words, each tick of the underlying clock may not be the same length (e.g.
/// some seconds may be longer than others). An instant may jump forwards or
/// experience time dilation (slow down or speed up), but it will never go
/// backwards.
///
/// Instants are opaque types that can only be compared to one another. There is
/// no method to get "the number of seconds" from an instant. Instead, it only
/// allows measuring the duration between two instants (or comparing two
/// instants).
///
/// Example:
///
/// ```no_run
/// use std::time::{Duration, Instant};
/// use std::thread::sleep;
///
/// fn main() {
///    let now = Instant::now();
///
///    // we sleep for 2 seconds
///    sleep(Duration::new(2, 0));
///    // it prints '2'
///    println!("{}", now.elapsed().as_secs());
/// }
/// ```
///
/// # OS-specific behaviors
///
/// An `Instant` is a wrapper around system-specific types and it may behave
/// differently depending on the underlying operating system. For example,
/// the following snippet is fine on Linux but panics on macOS:
///
/// ```no_run
/// use ksched::time::{Instant, Duration};
///
/// let now = Instant::now();
/// let max_nanoseconds = u64::MAX / 1_000_000_000;
/// let duration = Duration::new(max_nanoseconds, 0);
/// println!("{:?}", now + duration);
/// ```
///
/// # Underlying System calls
/// Currently, the following system calls are being used to get the current time using `now()`:
///
/// |  Platform |               System call                                            |
/// |:---------:|:--------------------------------------------------------------------:|
/// | SGX       | [`insecure_time` usercall]. More information on [timekeeping in SGX] |
/// | UNIX      | [clock_gettime (Monotonic Clock)]                                    |
/// | Darwin    | [mach_absolute_time]                                                 |
/// | VXWorks   | [clock_gettime (Monotonic Clock)]                                    |
/// | WASI      | [__wasi_clock_time_get (Monotonic Clock)]                            |
/// | Windows   | [QueryPerformanceCounter]                                            |
///
/// [QueryPerformanceCounter]: https://docs.microsoft.com/en-us/windows/win32/api/profileapi/nf-profileapi-queryperformancecounter
/// [`insecure_time` usercall]: https://edp.fortanix.com/docs/api/fortanix_sgx_abi/struct.Usercalls.html#method.insecure_time
/// [timekeeping in SGX]: https://edp.fortanix.com/docs/concepts/rust-std/#codestdtimecode
/// [__wasi_clock_time_get (Monotonic Clock)]: https://github.com/WebAssembly/WASI/blob/master/phases/snapshot/docs.md#clock_time_get
/// [clock_gettime (Monotonic Clock)]: https://linux.die.net/man/3/clock_gettime
/// [mach_absolute_time]: https://developer.apple.com/library/archive/documentation/Darwin/Conceptual/KernelProgramming/services/services.html
///
/// **Disclaimer:** These system calls might change over time.
///
/// > Note: mathematical operations like [`add`] may panic if the underlying
/// > structure cannot represent the new point in time.
///
/// [`add`]: Instant::add
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Instant(Duration);

impl Instant {
    /// Returns an instant corresponding to "now".
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Instant;
    ///
    /// let now = Instant::now();
    /// ```
    pub fn now() -> Instant {
        let t = if let Some(f) = T.lock().as_ref() {
            f()
        } else {
            Duration::new(0, 0)
        };
        Instant(t)
    }

    /// Returns the amount of time elapsed from another instant to this one.
    ///
    /// # Panics
    ///
    /// This function will panic if `earlier` is later than `self`.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::time::{Duration, Instant};
    /// use std::thread::sleep;
    ///
    /// let now = Instant::now();
    /// sleep(Duration::new(1, 0));
    /// let new_now = Instant::now();
    /// println!("{:?}", new_now.duration_since(now));
    /// ```
    pub fn duration_since(&self, earlier: Instant) -> Duration {
        self.0
            .checked_sub(earlier.0)
            .expect("supplied instant is later than self")
    }

    /// Returns the amount of time elapsed from another instant to this one,
    /// or None if that instant is later than this one.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::time::{Duration, Instant};
    /// use std::thread::sleep;
    ///
    /// let now = Instant::now();
    /// sleep(Duration::new(1, 0));
    /// let new_now = Instant::now();
    /// println!("{:?}", new_now.checked_duration_since(now));
    /// println!("{:?}", now.checked_duration_since(new_now)); // None
    /// ```
    pub fn checked_duration_since(&self, earlier: Instant) -> Option<Duration> {
        self.0.checked_sub(earlier.0)
    }

    /// Returns the amount of time elapsed from another instant to this one,
    /// or zero duration if that instant is later than this one.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::time::{Duration, Instant};
    /// use std::thread::sleep;
    ///
    /// let now = Instant::now();
    /// sleep(Duration::new(1, 0));
    /// let new_now = Instant::now();
    /// println!("{:?}", new_now.saturating_duration_since(now));
    /// println!("{:?}", now.saturating_duration_since(new_now)); // 0ns
    /// ```
    pub fn saturating_duration_since(&self, earlier: Instant) -> Duration {
        self.checked_duration_since(earlier).unwrap_or_default()
    }

    /// Returns the amount of time elapsed since this instant was created.
    ///
    /// # Panics
    ///
    /// This function may panic if the current time is earlier than this
    /// instant, which is something that can happen if an `Instant` is
    /// produced synthetically.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::thread::sleep;
    /// use std::time::{Duration, Instant};
    ///
    /// let instant = Instant::now();
    /// let three_secs = Duration::from_secs(3);
    /// sleep(three_secs);
    /// assert!(instant.elapsed() >= three_secs);
    /// ```
    pub fn elapsed(&self) -> Duration {
        Instant::now() - *self
    }

    /// Returns `Some(t)` where `t` is the time `self + duration` if `t` can be represented as
    /// `Instant` (which means it's inside the bounds of the underlying data structure), `None`
    /// otherwise.
    pub fn checked_add(&self, duration: Duration) -> Option<Instant> {
        self.0.checked_add(duration).map(|t| Instant(t))
    }

    /// Returns `Some(t)` where `t` is the time `self - duration` if `t` can be represented as
    /// `Instant` (which means it's inside the bounds of the underlying data structure), `None`
    /// otherwise.
    pub fn checked_sub(&self, duration: Duration) -> Option<Instant> {
        self.0.checked_sub(duration).map(|t| Instant(t))
    }
}

impl Add<Duration> for Instant {
    type Output = Instant;

    /// # Panics
    ///
    /// This function may panic if the resulting point in time cannot be represented by the
    /// underlying data structure. See [`Instant::checked_add`] for a version without panic.
    fn add(self, other: Duration) -> Instant {
        self.checked_add(other)
            .expect("overflow when adding duration to instant")
    }
}

impl AddAssign<Duration> for Instant {
    fn add_assign(&mut self, other: Duration) {
        *self = *self + other;
    }
}

impl Sub<Duration> for Instant {
    type Output = Instant;

    fn sub(self, other: Duration) -> Instant {
        self.checked_sub(other)
            .expect("overflow when subtracting duration from instant")
    }
}

impl SubAssign<Duration> for Instant {
    fn sub_assign(&mut self, other: Duration) {
        *self = *self - other;
    }
}

impl Sub<Instant> for Instant {
    type Output = Duration;

    fn sub(self, other: Instant) -> Duration {
        self.duration_since(other)
    }
}

impl fmt::Debug for Instant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
