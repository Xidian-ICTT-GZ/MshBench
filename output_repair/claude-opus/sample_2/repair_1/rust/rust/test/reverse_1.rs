predicate list_segment(ptr: *mut Node, end: *mut Node) =
  ptr == end ? emp : 
  ptr != null_ptr() ? 
    (ptr as *mut Node) -> Node { next: ?next } ** list_segment(next, end)
  : false;

struct Node {
    next: *mut Node,
}

impl Node {
    #[requires(list_segment(n, null_ptr()))]
    #[ensures(list_segment(result, null_ptr()))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        loop {
            #[invariant(list_segment(m, null_ptr()) ** list_segment(n, null_ptr()))]
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