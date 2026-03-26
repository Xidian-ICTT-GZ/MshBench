struct Node {
    next: *mut Node,
}

pred node(n: *mut Node, next: *mut Node) = n != std::ptr::null_mut() && (*n).next |-> next;

pred nodes(n: *mut Node; ns: list<*mut Node>) =
    match ns {
        cons(h, t) => node(n, h) * nodes(h, t),
        nil => n == std::ptr::null_mut(),
    };

impl Node {
    #[requires(nodes(n, nodes))]
    #[ensures(nodes(result, reverse(nodes)))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        #[invariant(nodes(n, xs) * nodes(m, ys) * eq(reverse(xs) ++ ys, reverse(nodes)))]
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