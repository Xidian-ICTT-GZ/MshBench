struct Node {
    next: *mut Node,
}

pred node(p: *mut Node; next: *mut Node) = (*p).next |-> next;

pred nodes(p: *mut Node; xs: list<*mut Node>) =
    match xs {
        nil => p == std::ptr::null_mut(),
        cons(h, t) => exists q. node(p, q) * nodes(q, t)
    };

impl Node {
    #[requires(nodes(n, xs))]
    #[ensures(nodes(result, reverse(xs)))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        proof_assert nodes(m, reverse(nil));
        #[invariant(exists ys. nodes(n, ys) * nodes(m, reverse(ys)) * xs == ys ++ reverse(reverse(ys)))]
        loop {
            if n.is_null() {
                return m;
            }
            let k = (*n).next;
            proof_obligation {
                // Before update: n points to a node whose next is k
                // We have node(n, k) as part of nodes(n, cons(n, rest))
                // and nodes(m, reverse(ys)) for current ys
            }
            (*n).next = m;
            proof_obligation {
                // Now n points to m, so we can form node(n, m)
                // and shift one element from n-list to m-list
            }
            m = n;
            n = k;
        }
    }
}