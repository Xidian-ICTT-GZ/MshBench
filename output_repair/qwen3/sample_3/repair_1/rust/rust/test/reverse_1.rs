predicate Nodes(*mut Node n; *mut Node tail) =
    match n {
        null => emp &*& tail == null,
        _ => (*n).next |-> ?next &*& Nodes(next, tail)
    };

impl Node {
    #[requires(Nodes(n, null))]
    #[ensures(Nodes(result, null))]
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