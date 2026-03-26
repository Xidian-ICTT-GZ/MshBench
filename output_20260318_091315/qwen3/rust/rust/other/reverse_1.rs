struct Node {
    next: *mut Node,
}

predicate Nodes(*mut Node n; *mut Node prev) =
    n == std::ptr::null_mut() ?
        emp
    :
        (*n).next |-> ?next &*& Nodes(next, n);

impl Node {

    #[requires(Nodes(n, std::ptr::null_mut()))]
    #[ensures(Nodes(result, std::ptr::null_mut()))]
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