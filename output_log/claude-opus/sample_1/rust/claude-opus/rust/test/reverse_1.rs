struct Node {
    next: *mut Node,
}

pred nodes(n: *mut Node; count: i32) =
    if n == std::ptr::null_mut() {
        count == 0
    } else {
        count > 0 &*&
        n != std::ptr::null_mut() &*&
        malloc_block_Node(n) &*&
        (*n).next |-> ?next &*&
        nodes(next, count - 1)
    };

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
            // open nodes(n, n_count) to access head
            open nodes(n, n_count);
            let k = (*n).next;

            (*n).next = m;

            m = n;
            n = k;
            // close nodes(m, m_count + 1)
            close nodes(m, m_count + 1);

            // close nodes(n, n_count - 1)
        }
    }
}