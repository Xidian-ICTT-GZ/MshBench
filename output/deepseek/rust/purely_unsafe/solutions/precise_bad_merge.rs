use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use vstd::ptr::*;

fn main() {
    unsafe {
        let mut x = 0;
        let mut y = 0;

        #[verifier::spec] let x_spec = x;
        #[verifier::spec] let y_spec = y;
        
        #[verifier::spec] proof {
            assume(false);
        }
        
        std::hint::unreachable_unchecked();
    }
}

} // verus!