/*@ pred node(p: *mut Node, next: *mut Node) = 
    p != 0 as *mut Node &*& 
    alloc_block_<Node>(p) &*& 
    struct_Node_padding(p) &*& 
    (*p).next |-> next;
@*/

/*@ pred nodes(p: *mut Node) = 
    p == 0 as *mut Node ? 
        true 
    : 
        node(p, ?next) &*& nodes(next);
@*/

impl Node {

    //@ req nodes(n);
    //@ ens nodes(result);
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    {
        let mut m = std::ptr::null_mut();
        //@ close nodes(m);
        loop {
            //@ open nodes(n);
            if n.is_null() {
                //@ open nodes(m);
                return m;
            }
            let k = (*n).next;
            //@ open node(n, _);
            (*n).next = m;
            //@ close node(n, m);
            m = n;
            n = k;
            //@ close nodes(m);
        }
    }

}