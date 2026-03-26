#![allow(non_snake_case)]

predicate list(p: *mut Node, len: usize) =
  if len == 0 {
    p.is_null()
  } else {
    exists next: *mut Node, 
      p.is_valid() && 
      (*p).next == next && 
      list(next, len - 1)
  };

struct Node {
    next: *mut Node,
}

impl Node {
    #[requires(list(n, len))]
    #[ensures(list(result, len))]
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