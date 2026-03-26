struct Node {
    next: *mut Node,
}

impl Node {
    #[requires(list_segment(n, std::ptr::null_mut()))]
    #[ensures(list_segment(result, std::ptr::null_mut()))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        loop {
            #[invariant(list_segment(m, std::ptr::null_mut()) ** list_segment(n, std::ptr::null_mut()))]
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