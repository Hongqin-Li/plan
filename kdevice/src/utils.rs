/// Convert slice to uint.
#[macro_export]
macro_rules! from_bytes {
    ($type:ty, $slice:expr) => {
        <$type>::from_le_bytes($slice.try_into().unwrap())
    };
}
