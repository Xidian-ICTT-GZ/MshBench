struct Node {
    next: *mut Node,
}

pred nodes(n: *mut Node; count: int) =
    n == std::ptr::null_mut()
        ? count == 0
        : count > 0 &*&
          n |-> Node { next: ?next } &*&
          nodes(next, count - 1);

impl Node {
    #[requires(nodes(n, ?count))]
    #[ensures(nodes(result, count))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        #[invariant(nodes(n, ?n_count) &*& nodes(m, ?m_count) &*& n_count + m_count == count)]
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