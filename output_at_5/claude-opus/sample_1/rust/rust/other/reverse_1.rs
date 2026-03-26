struct Node {
    next: *mut Node,
}

// verifast_options{}

//@ pred node(self: *mut Node) = self != 0 && pointer(self, _) &*& \true;

impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ requires true;
    //@ ensures true;
    {
        let mut m = std::ptr::null_mut();
        loop 
        //@ invariant node(m) &*& node(n) || m == std::ptr::null_mut() &*& node(n) || node(m) &*& n == std::ptr::null_mut() || m == std::ptr::null_mut() &*& n == std::ptr::null_mut();
        {
            
            if n.is_null() {
                return m;
            }
            let k = (*n).next;
            //@ open node(n);
            (*n).next = m;
            //@ close node(n);
            m = n;
            n = k;
        }
    }

}