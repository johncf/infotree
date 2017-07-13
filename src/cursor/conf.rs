use arrayvec::Array;

use node::{NodesPtr, Arc16, Rc16, Box16};
use traits::Leaf;
use super::{CStep, CMutStep};

pub trait PtrMark<L: Leaf>: Sized {
    type Ptr: NodesPtr<L>;
}

pub trait CConf<'a, L: Leaf + 'a, PI>: Sized + PtrMark<L>
    where Self::Ptr: 'a,
{
    type StepsBuf: Array<Item=CStep<'a, L, PI, Self>>;
}

pub trait CMutConf<L: Leaf, PI>: Sized + PtrMark<L> {
    type MutStepsBuf: Array<Item=CMutStep<L, PI, Self>>;
}

// Minimum number of leaves required to exceed a cursor with {Arc,Rc,Box}33M conf
//     = max_width * min_width^(height - 1)
//     = 16 * 8^7 = 2^25 = ~33.6M
def_cursor_conf!(Arc33M, Arc16, 8);
def_cursor_conf!(Rc33M, Rc16, 8);
def_cursor_conf!(Box33M, Box16, 8);
