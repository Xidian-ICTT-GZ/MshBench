struct Node {
    next: *mut Node,
}

predicate list(p: *mut Node, len: usize) =
    p.is_null() ? len == 0 : 
    (
        exists n: *mut Node;
        p != null_ptr &&
        (p as *mut Node).next |-> n &&
        list(n, len - 1)
    );

impl Node {
    #[requires(list(n, _))]
    #[ensures(list(result, _))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
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