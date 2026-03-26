struct Node {
    next: *mut Node,
}

#[predicate]
fn node(n: *mut Node) -> bool {
    exists!<next: *mut Node>; n != std::ptr::null_mut() && struct_Node! { n => Node { next } } && node(next)
}

#[predicate]
fn lseg(start: *mut Node, end: *mut Node) -> bool {
    start == end && emp
    ||
    start != std::ptr::null_mut() && exists!<next: *mut Node>; struct_Node! { start => Node { next } } && lseg(next, end)
}

#[predicate]
fn lseg_rev(start: *mut Node, end: *mut Node, rev: *mut Node) -> bool {
    start == end && rev == std::ptr::null_mut() && emp
    ||
    start != std::ptr::null_mut() && exists!<next: *mut Node>; struct_Node! { start => Node { next } } && lseg_rev(next, end, start) && start->next == rev
}

#[lemma]
fn lseg_rev_append(start: *mut Node, end: *mut Node, rev: *mut Node)
    requires lseg_rev(start, end, rev);
    ensures lseg(start, end);
{
    open lseg_rev(start, end, rev);
    if start == end {
        close lseg(start, end);
    } else {
        let next = ghost! { ?next };
        lseg_rev_append(next, end, start);
        close lseg(start, end);
    }
}

#[lemma]
fn lseg_split(start: *mut Node, end: *mut Node, mid: *mut Node)
    requires lseg(start, end) && start != end && start != mid;
    ensures lseg(start, mid) * lseg(mid, end);
{
    open lseg(start, end);
    if start == end {
        // contradiction
    } else {
        let next = ghost! { ?next };
        if start == mid {
            close lseg(start, mid);
            close lseg(mid, end);
        } else {
            lseg_split(next, end, mid);
            close lseg(start, mid);
        }
    }
}

#[lemma]
fn lseg_join(start: *mut Node, mid: *mut Node, end: *mut Node)
    requires lseg(start, mid) * lseg(mid, end);
    ensures lseg(start, end);
{
    open lseg(start, mid);
    if start == mid {
        open lseg(mid, end);
        close lseg(start, end);
    } else {
        let next = ghost! { ?next };
        lseg_join(next, mid, end);
        close lseg(start, end);
    }
}

impl Node {
    #[requires(lseg(n, std::ptr::null_mut()))]
    #[ensures(lseg(result, std::ptr::null_mut()))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        #[invariant(lseg_rev(n, std::ptr::null_mut(), m))]
        loop {
            if n.is_null() {
                lseg_rev_append(n, std::ptr::null_mut(), m);
                return m;
            }
            let k = (*n).next;

            (*n).next = m;
            m = n;
            n = k;
        }
    }
}