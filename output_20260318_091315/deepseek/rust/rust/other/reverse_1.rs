struct Node {
    next: *mut Node,
}

#[predicate]
fn node(n: *mut Node) -> bool {
    exists!((next: *mut Node) => struct_Node_pat!(n) = Node { next } &*& n != 0)
}

#[predicate]
fn lseg(first: *mut Node, last: *mut Node) -> bool {
    if first == last {
        true
    } else {
        node(first) &*&
        exists!((next: *mut Node) => (*first).next |-> next &*& lseg(next, last))
    }
}

#[predicate]
fn lseg_full(first: *mut Node, last: *mut Node) -> bool {
    lseg(first, last) &*& if first == last { true } else { node(first) }
}

#[lemma]
fn lseg_split(first: *mut Node, mid: *mut Node, last: *mut Node)
    requires lseg(first, last) &*& first != last &*& mid != 0;
    ensures lseg(first, mid) &*& lseg(mid, last);
{}

#[lemma]
fn lseg_join(first: *mut Node, mid: *mut Node, last: *mut Node)
    requires lseg(first, mid) &*& lseg(mid, last);
    ensures lseg(first, last);
{}

#[lemma]
fn lseg_null_is_empty(p: *mut Node)
    requires lseg(p, std::ptr::null_mut());
    ensures p == std::ptr::null_mut();
{}

impl Node {
    #[requires(lseg(n, std::ptr::null_mut()))]
    #[ensures(lseg(result, std::ptr::null_mut()))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        #[invariant(lseg(m, std::ptr::null_mut()) &*& lseg(n, std::ptr::null_mut()))]
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