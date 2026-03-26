struct Node {
    next: *mut Node,
}

//@ predicate nodes_list(struct Node* n;) = n == NULL ? emp : malloc_block_Node(n, _) &*& nodes_list((*n).next);
impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ requires nodes_list(n);
    //@ ensures nodes_list(result);
    {
        let mut m = std::ptr::null_mut();
        //@ open nodes_list(n);
        loop {
            if n.is_null() {
                //@ close nodes_list(m);
                return m;
            }
            let k = (*n).next;
            //@ open nodes_list(n);
            (*n).next = m;
            m = n;
            n = k;
            //@ close nodes_list(m);
        }
    }

}