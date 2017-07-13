#![allow(unused_macros)]

macro_rules! def_nodes_ptr_rc {
    ($wrap:tt, $rc:tt, $size:expr) => {
        #[derive(Clone)]
        pub struct $wrap<L: Leaf>($rc<ArrayVec<[Node<L, $wrap<L>>; $size]>>);

        impl<L: Leaf> NodesPtr<L> for $wrap<L> {
            type Array = [Node<L, $wrap<L>>; $size];

            fn new(nodes: ArrayVec<Self::Array>) -> Self {
                $wrap($rc::new(nodes))
            }

            fn make_mut(this: &mut Self) -> &mut ArrayVec<Self::Array> {
                $rc::make_mut(&mut this.0)
            }
        }

        impl<L: Leaf> Deref for $wrap<L> {
            type Target = [Node<L, $wrap<L>>];

            fn deref(&self) -> &[Node<L, $wrap<L>>] {
                &*self.0
            }
        }
    }
}

macro_rules! def_nodes_ptr_box {
    ($wrap:tt, $size:expr) => {
        #[derive(Clone)]
        pub struct $wrap<L: Leaf>(Box<ArrayVec<[Node<L, $wrap<L>>; $size]>>);

        impl<L: Leaf> NodesPtr<L> for $wrap<L> {
            type Array = [Node<L, $wrap<L>>; $size];

            fn new(nodes: ArrayVec<Self::Array>) -> Self {
                $wrap(Box::new(nodes))
            }

            fn make_mut(this: &mut Self) -> &mut ArrayVec<Self::Array> {
                &mut *this.0
            }
        }

        impl<L: Leaf> Deref for $wrap<L> {
            type Target = [Node<L, $wrap<L>>];

            fn deref(&self) -> &[Node<L, $wrap<L>>] {
                &*self.0
            }
        }
    }
}

macro_rules! def_cursor_conf {
    ($wrap:tt, $ptr:tt, $buf:expr) => {
        pub enum $wrap {}
        impl<L: Leaf> PtrMark<L> for $wrap {
            type Ptr = $ptr<L>;
        }
        impl<'a, L: Leaf + 'a, PI> CConf<'a, L, PI> for $wrap {
            type StepsBuf = [CStep<'a, L, PI, Self>; $buf];
        }
        impl<L: Leaf, PI> CMutConf<L, PI> for $wrap {
            type MutStepsBuf = [CMutStep<L, PI, Self>; $buf];
        }
    }
}

#[cfg(test)]
macro_rules! testln {
    ($fmt:expr) => {
        println!(concat!("DBG[{}:{}]: ", $fmt), file!(), line!())
    };
    ($fmt:expr, $($arg:tt)*) => {
        println!(concat!("DBG[{}:{}]: ", $fmt), file!(), line!(), $($arg)*)
    };
}

#[cfg(not(test))]
macro_rules! testln {
    ($fmt:expr) => ();
    ($fmt:expr, $($arg:tt)*) => ();
}
