struct Node {
    next: *mut Node,
}

/*@

pred nodes(struct Node* n, struct Node* last) =
    n == last ?
        true
    :
        n != 0 &*& (*n).next |-> ?next &*& struct_Node_padding(n) &*& nodes(next, last);

@*/

impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ req nodes(n, 0);
    //@ ens nodes(result, 0);
    {
        let mut m = std::ptr::null_mut();
        //@ close nodes(m, 0);
        loop {
            //@ inv nodes(n, 0) &*& nodes(m, 0);
            if n.is_null() {
                //@ open nodes(n, 0);
                return m;
            }
            //@ open nodes(n, 0);
            let k = (*n).next;

            (*n).next = m;
            //@ close nodes(n, k);
            m = n;
            n = k;
            //@ open nodes(m, k);
            //@ close nodes(m, 0);
        }
    }

}