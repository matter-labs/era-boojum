#[macro_export]
#[cfg(feature = "log_tracing")]
macro_rules! log {
    ($($arg:tt)*) => {
        tracing::trace!($($arg)*)
    };
}

#[macro_export]
#[cfg(not(feature = "log_tracing"))]
macro_rules! log {
    ($($arg:tt)*) => {
        println!($($arg)*)
    };
}
