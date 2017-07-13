mod view;
//mod edit;
mod nav;
pub mod conf;

pub use self::nav::actions;

pub use self::view::Cursor;
//pub use self::edit::CursorMut;
pub use self::nav::CursorNav;

#[doc(hidden)]
pub use self::view::CStep;
//#[doc(hidden)]
//pub use self::edit::CMutStep;
