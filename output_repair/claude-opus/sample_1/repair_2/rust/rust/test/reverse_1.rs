struct Node {
    next: *mut Node,
}

impl Node {
    #[requires(list(n, _))]
    #[ensures(list(result, _))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        loop {
            #[invariant(list(n, _) * list(m, _))]
            {
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
}