pred Node(p: *mut Node; next: *mut Node) = (*p).next |-> next;

pred Nodes(p: *mut Node; xs: list<*mut Node>) =
    match xs {
        nil => p == std::ptr::null_mut(),
        cons(h, t) => exists q. Node(p, q) * Nodes(q, t)
    };

impl Node {
    #[requires(Nodes(n, xs))]
    #[ensures(Nodes(result, reverse(xs)))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        #[invariant(Nodes(n, ys) * Nodes(m, reverse(xs_minus_ys)))]
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