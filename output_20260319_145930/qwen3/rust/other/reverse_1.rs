/*@ pred node(node: *mut Node, next: *mut Node) = alloc_block_node(node) &*& struct_Node_padding(node) &*& (*node).next |-> next; @*/

impl Node {

    //@ req true;
    //@ ens true;
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    {
        let mut m = std::ptr::null_mut();
        //@ open node(_, _) => _;
        loop {
            //@ inv n == 0 ? m == 0 : true;
            if n.is_null() {
                return m;
            }
            let k = (*n).next;
            //@ open node(n, _);
            (*n).next = m;
            //@ close node(n, m);
            m = n;
            n = k;
        }
    }

}