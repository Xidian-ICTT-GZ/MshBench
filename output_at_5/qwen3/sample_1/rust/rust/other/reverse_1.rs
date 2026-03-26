struct Node {
    next: *mut Node,
}

impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ requires true;
    //@ ensures true;
    {
        let mut m = std::ptr::null_mut();
        loop {
            if n.is_null() {
                return m;
            }
            let k = (*n).next;
            (*n).next = m;
            m = n;
            n = k;
        }
    }

}