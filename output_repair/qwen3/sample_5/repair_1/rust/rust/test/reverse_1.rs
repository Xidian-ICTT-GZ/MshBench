pred Node(node: *mut Node, next: *mut Node) = (*node).next |-> next;

pred Nodes(node: *mut Node, nodes: list<*mut Node>) =
    match nodes {
        cons(hd, tl) => Node(node, hd) * Nodes(hd, tl),
        nil => node == std::ptr::null_mut(),
    };

impl Node {
    #[requires(Nodes(n, ns))]
    #[ensures(Nodes(result, reverse(ns)))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        #[invariant(Nodes(n, ns1) * Nodes(m, ns2) * eq(reverse(ns2) ++ ns1, ns))]
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