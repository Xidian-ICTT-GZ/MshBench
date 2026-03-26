struct Node {
    next: *mut Node,
}

#[predicate]
fn list_segment(p: *mut Node, q: *mut Node) -> bool;

#[axiom]
fn list_segment_nil(p: *mut Node)
    (ensures list_segment(p, p));

#[axiom]
fn list_segment_cons(p: *mut Node, q: *mut Node, r: *mut Node)
    (requires p != std::ptr::null_mut() && list_segment((*p).next, q))
    (ensures list_segment(p, q));

#[axiom]
fn list_segment_append(p: *mut Node, q: *mut Node, r: *mut Node)
    (requires list_segment(p, q) && list_segment(q, r))
    (ensures list_segment(p, r));

#[axiom]
fn list_segment_inv(p: *mut Node, q: *mut Node)
    (requires list_segment(p, q))
    (ensures p == q || (p != std::ptr::null_mut() && list_segment((*p).next, q)));

impl Node {
    #[requires(list_segment(n, std::ptr::null_mut()))]
    #[ensures(list_segment(result, std::ptr::null_mut()))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        #[invariant(list_segment(n, std::ptr::null_mut()) && list_segment(m, std::ptr::null_mut()))]
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