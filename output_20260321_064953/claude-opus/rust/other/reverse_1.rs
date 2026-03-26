struct Node {
    next: *mut Node,
}

/*@
pred Nodes(n: *mut Node;) =
    if n == 0 {
        true
    } else {
        (*n).next |-> ?next &*& struct_Node_padding(n) &*& alloc_block_Node(n) &*& Nodes(next)
    };
@*/

impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ req Nodes(n);
    //@ ens Nodes(result);
    {
        let mut m = std::ptr::null_mut();
        //@ close Nodes(m);
        loop {
            //@ inv Nodes(n) &*& Nodes(m);
            //@ open Nodes(n);
            if n.is_null() {
                return m;
            }
            let k = (*n).next;
            //@ open Nodes(k);
            (*n).next = m;
            //@ close Nodes(k);
            //@ close Nodes(n);
            m = n;
            n = k;
        }
    }

}