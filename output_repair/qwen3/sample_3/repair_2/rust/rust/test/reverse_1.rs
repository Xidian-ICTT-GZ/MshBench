struct Node {
    next: *mut Node,
}

predicate Nodes(*mut Node n; *mut Node tail) =
    if n == std::ptr::null_mut() {
        emp &*& tail == std::ptr::null_mut()
    } else {
        (*n).next |-> ?next &*& Nodes(next, tail)
    };

impl Node {
    #[requires(Nodes(n, std::ptr::null_mut()))]
    #[ensures(Nodes(result, std::ptr::null_mut()))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        #[invariant(Nodes(n, ?tail) &*& Nodes(m, tail))]
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