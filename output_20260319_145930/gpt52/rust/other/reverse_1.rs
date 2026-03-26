struct Node {
    next: *mut Node,
}

/*@

pred nodes(mut n: *mut Node) =
    n == 0 ?
        true
    :
        alloc_block_Node(n) &*& (*n).next |-> ?next &*& nodes(next);

@*/

impl Node {

    //@ req nodes(n);
    //@ ens nodes(result);
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ ensures nodes(result);
    {
        //@ open nodes(n);
        let mut m = std::ptr::null_mut();
        //@ close nodes(m);
        loop {
            //@ inv nodes(m) &*& nodes(n);
            //@ open nodes(n);
            if n.is_null() {
                //@ close nodes(n);
                return m;
            }
            let k = (*n).next;

            (*n).next = m;
            //@ close nodes(n);
            m = n;
            n = k;
        }
    }

}