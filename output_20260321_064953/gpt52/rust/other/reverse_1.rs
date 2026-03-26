struct Node {
    next: *mut Node,
}

/*@

pred nodes(struct Node *n) =
    n == 0 ?
        true
    :
        (*n).next |-> ?next &*& nodes(next);

@*/

impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ req nodes(n);
    //@ ens nodes(result);
    {
        let mut m = std::ptr::null_mut();
        //@ close nodes(m);
        loop {
            //@ inv nodes(n) &*& nodes(m);
            if n.is_null() {
                //@ open nodes(n);
                return m;
            }
            //@ open nodes(n);
            let k = (*n).next;

            (*n).next = m;
            //@ close nodes(n);
            m = n;
            n = k;
        }
    }

}