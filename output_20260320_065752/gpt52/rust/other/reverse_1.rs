struct Node {
    next: *mut Node,
}

/*@

pred nodes(mut n: *mut Node) =
    n == 0 ?
        true
    :
        std::alloc::alloc_block(n as *u8, std::alloc::Layout::new_::<Node>()) &*&
        (*n).next |-> ?next &*&
        nodes(next);

@*/

impl Node {

    //@ req nodes(n);
    //@ ens nodes(result);
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    {
        //@ open nodes(n);
        let mut m = std::ptr::null_mut();
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
            //@ open nodes(n);
            m = n;
            n = k;
            //@ close nodes(m);
        }
    }

}