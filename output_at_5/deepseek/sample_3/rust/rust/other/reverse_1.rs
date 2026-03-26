struct Node {
    next: *mut Node,
}

//@ predicate node(struct Node* node; struct Node* next) = node != 0 &*& struct_Node_padding(node) &*& (*node).next |-> next;

impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ req node(n, _);
    //@ ens node(result, _);
    {
        let mut m = std::ptr::null_mut();
        loop 
        //@ inv node(n, _) &*& node(m, _);
        {
            //@ open node(n, _);
            if n.is_null() {
                //@ close node(n, _);
                return m;
            }
            let k = (*n).next;
            //@ open node(k, _);
            (*n).next = m;
            m = n;
            n = k;
            //@ close node(m, _);
        }
    }

}