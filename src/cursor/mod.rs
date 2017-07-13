use arrayvec::ArrayVec;

mod view;
mod edit;
mod nav;

pub use self::nav::actions;

pub use self::view::Cursor;
pub use self::edit::CursorMut;
pub use self::nav::CursorNav;

// Maximum height of tree that can be handled by cursor types.
const CURSOR_MAX_HT: usize = 8;
// => Minimum number of leaves required to exceed a cursor with the above capacity
//          = MAX * MIN^(CURSOR_MAX_HT - 1)
//          = 16 * 8^7 = 2^25 = ~33.5M (for {Arc,Box,Rc}16)

type CVec<T> = ArrayVec<[T; CURSOR_MAX_HT]>;
