struct Node {
    next: *mut Node,
}

predicate node(node: *mut Node, next: *mut Node) = (*node).next |-> next;

predicate nodes(node: *mut Node, ns: list<*mut Node>) =
    match ns {
        cons(hd, tl) => node(node, hd) * nodes(hd, tl),
        nil => node == std::ptr::null_mut(),
    };

impl Node {
    #[requires(nodes(n, ns))]
    #[ensures(nodes(result, reverse(ns)))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        #[invariant(nodes(n, ns1) * nodes(m, ns2) * eq(reverse(ns2) ++ ns1, ns))]
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