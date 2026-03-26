#![feature(stmt_expr_attributes)]

struct Node {
    next: *mut Node,
}

predicate list(p: *mut Node, len: usize) =
    match len {
        0 => p.is_null(),
        _ => exists next_p: *mut Node, 
             p.is_null() == false &&
             (p as *const Node).next |-> next_p &&
             list(next_p, len - 1)
    };

impl Node {
    #[requires(list(n, len))]
    #[ensures(list(result, len))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        loop {
            #[invariant(exists len_n: usize, exists len_m: usize, 
                       list(n, len_n) * list(m, len_m) * (len_n + len_m == len))]
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