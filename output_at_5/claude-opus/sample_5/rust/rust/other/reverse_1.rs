struct Node {
    next: *mut Node,
}

// verifast_options{}

//@ predicate node(n: *mut Node) = n != std::ptr::null_mut() &*& n->Node.next |-> ?next &*& (next == std::ptr::null_mut() || node(next));

impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ requires n == std::ptr::null_mut() || node(n);
    //@ ensures result == std::ptr::null_mut() || node(result);
    {
        let mut m = std::ptr::null_mut();
        //@ while (true)
        //@ invariant (m == std::ptr::null_mut() || node(m)) &*& (n == std::ptr::null_mut() || node(n));
        {
            if n.is_null() {
                //@ assert n == std::ptr::null_mut();
                return m;
            }
            //@ open node(n);
            let k = (*n).next;
            (*n).next = m;
            //@ close node(n);
            m = n;
            n = k;
        }
    }

}