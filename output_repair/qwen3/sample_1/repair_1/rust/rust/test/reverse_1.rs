pred Node(n: *mut Node, next: *mut Node) = (*n).next |-> next;

pred Nodes(n: *mut Node; nodes: list<*mut Node>) =
    match nodes {
        cons(h, t) => Node(n, h) * Nodes(h, t),
        nil => n == std::ptr::null_mut(),
    };

impl Node {
    #[requires(Nodes(n, nodes))]
    #[ensures(Nodes(result, reverse(nodes)))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        #[invariant(Nodes(n, xs) * Nodes(m, ys) * eq(reverse(xs) ++ ys, reverse(nodes)))]
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