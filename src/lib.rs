//! Provides a generic framework for building copy-on-write B-Tree-like structures.
//!
//! The design and implementation was inspired by [xi-rope].
//!
//! [xi-rope]: https://github.com/google/xi-editor/tree/master/rust/rope
extern crate arrayvec;
extern crate mines;

#[macro_use]
mod macros;

pub mod cursor;
pub mod node;
pub mod traits;
pub mod list;

#[cfg(test)]
extern crate rand;

#[cfg(test)]
mod test_help;
