#[cfg(test)]
#[macro_export]
macro_rules! testln {
    ($fmt:expr) => {
        println!(concat!("DBG[{}:{}]: ", $fmt), file!(), line!())
    };
    ($fmt:expr, $($arg:tt)*) => {
        println!(concat!("DBG[{}:{}]: ", $fmt), file!(), line!(), $($arg)*)
    };
}

#[cfg(not(test))]
#[macro_export]
macro_rules! testln {
    ($fmt:expr) => ();
    ($fmt:expr, $($arg:tt)*) => ();
}
