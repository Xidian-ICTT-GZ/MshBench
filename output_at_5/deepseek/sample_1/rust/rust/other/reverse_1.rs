struct Node {
    next: *mut Node,
}

//@ predicate node(struct Node* node; struct Node* next) = node != 0 &*& struct_Node_padding(node) &*& (*node).next |-> next;

impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ req node(n, ?next0) &*& node(next0, ?next1) &*& node(next1, ?next2) &*& node(next2, ?next3) &*& node(next3, ?next4) &*& node(next4, ?next5) &*& node(next5, ?next6) &*& node(next6, ?next7) &*& node(next7, ?next8) &*& node(next8, ?next9) &*& node(next9, 0);
    //@ ens node(result, ?rnext0) &*& node(rnext0, ?rnext1) &*& node(rnext1, ?rnext2) &*& node(rnext2, ?rnext3) &*& node(rnext3, ?rnext4) &*& node(rnext4, ?rnext5) &*& node(rnext5, ?rnext6) &*& node(rnext6, ?rnext7) &*& node(rnext7, ?rnext8) &*& node(rnext8, ?rnext9) &*& node(rnext9, 0);
    {
        let mut m = std::ptr::null_mut();
        loop {
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
        }
    }

}