struct Node {
    next: *mut Node,
}

#[predicate]
fn node(n: *mut Node) -> bool {
    exists!((next: *mut Node) => struct_Node_pat!(n) { next } &*& true)
}

#[predicate]
fn lseg(start: *mut Node, end: *mut Node) -> bool {
    start == end ? true : node(start) &*& lseg((*start).next, end)
}

#[predicate]
fn lseg_with_tail(start: *mut Node, end: *mut Node, tail: *mut Node) -> bool {
    start == end ? tail == std::ptr::null_mut() : node(start) &*& (*start).next == tail &*& lseg(tail, end)
}

#[lemma]
fn lseg_split(n: *mut Node, m: *mut Node, k: *mut Node)
    requires lseg(n, m) &*& m != k &*& lseg(m, k);
    ensures lseg(n, k);
{
    open lseg(n, m);
    if n != m {
        open node(n);
        lseg_split((*n).next, m, k);
        close lseg(n, k);
    } else {
        close lseg(n, k);
    }
}

#[lemma]
fn lseg_append(n: *mut Node, m: *mut Node, k: *mut Node)
    requires lseg(n, m) &*& lseg(m, k);
    ensures lseg(n, k);
{
    open lseg(n, m);
    if n != m {
        open node(n);
        lseg_append((*n).next, m, k);
        close lseg(n, k);
    } else {
        close lseg(n, k);
    }
}

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