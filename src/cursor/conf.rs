use arrayvec::Array;

use node::{NodesPtr, Arc16, Rc16};
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

// Minimum number of leaves required to exceed a cursor with Arc33M conf
//     = max_width * min_width^(height - 1)
//     = 16 * 8^7 = 2^25 = ~33.6M
pub enum Arc33M {}
impl<L: Leaf> PtrMark<L> for Arc33M {
    type Ptr = Arc16<L>;
}
impl<'a, L: Leaf + 'a, PI> CConf<'a, L, PI> for Arc33M {
    #[doc(hidden)]
    type StepsBuf = [CStep<'a, L, PI, Self>; 8];
}
impl<L: Leaf, PI> CMutConf<L, PI> for Arc33M {
    #[doc(hidden)]
    type MutStepsBuf = [CMutStep<L, PI, Self>; 8];
}

pub enum Rc33M {}
impl<L: Leaf> PtrMark<L> for Rc33M {
    type Ptr = Rc16<L>;
}
impl<'a, L: Leaf + 'a, PI> CConf<'a, L, PI> for Rc33M {
    #[doc(hidden)]
    type StepsBuf = [CStep<'a, L, PI, Self>; 8];
}
impl<L: Leaf, PI> CMutConf<L, PI> for Rc33M {
    #[doc(hidden)]
    type MutStepsBuf = [CMutStep<L, PI, Self>; 8];
}
