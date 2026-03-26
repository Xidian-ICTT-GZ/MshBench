struct Node {
    next: *mut Node,
}

/*@

pred nodes(n: *mut Node) =
    n == 0 ?
        true
    :
        (*n).next |-> ?next &*& nodes(next);

@*/

impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ req true;
    //@ ens true;
    {
        let mut m = std::ptr::null_mut();
        loop {
            if n.is_null() {
                return m;
            }
            let k = (*n).next;
            (*n).next = m;
            m = n;
            n = k;
        }
    }

}