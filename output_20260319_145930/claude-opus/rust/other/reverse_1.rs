struct Node {
    next: *mut Node,
}

/*@
pred Nodes(n: *mut Node; count: i32) =
    if n == 0 {
        count == 0
    } else {
        alloc_block_Node(n) &*&
        (*n).next |-> ?next &*&
        Nodes(next, ?rest) &*&
        count == rest + 1
    };
@*/

impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ req Nodes(n, ?count);
    //@ ens Nodes(result, count);
    {
        let mut m = std::ptr::null_mut();
        //@ close Nodes(m, 0);
        loop {
            //@ inv Nodes(n, ?n_count) &*& Nodes(m, ?m_count) &*& n_count + m_count == count;
            //@ open Nodes(n, n_count);
            if n.is_null() {
                return m;
            }
            let k = (*n).next;
            //@ open Nodes(k, _);
            //@ close Nodes(k, _);
            (*n).next = m;
            //@ close Nodes(n, m_count + 1);
            m = n;
            n = k;
        }
    }

}