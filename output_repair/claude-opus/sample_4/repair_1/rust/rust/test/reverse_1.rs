predicate list(p: *mut Node, len: usize) =
  len == 0 ? p.is_null() : !p.is_null() && ((*p).next, list((*p).next, len - 1));

struct Node {
    next: *mut Node,
}

impl Node {
    #[requires(list(n, len))]
    #[ensures(list(result, len))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        loop {
            #[invariant(exists len_n: usize, exists len_m: usize, list(n, len_n) * list(m, len_m))]
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