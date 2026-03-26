struct Node {
    next: *mut Node,
}

/*@

predicate nodes(*mut Node n; *mut Node end) =
    n == end ?
        emp
    :
        n->next |-> ?next &*& nodes(next, end);

lemma void nodes_unfold_nonnull(*mut Node n, *mut Node end)
    requires nodes(n, end) &*& n != end;
    ensures n->next |-> ?next &*& nodes(next, end);
{
    open nodes(n, end);
}

lemma void nodes_fold_nonnull(*mut Node n, *mut Node end, *mut Node next)
    requires n->next |-> next &*& nodes(next, end) &*& n != end;
    ensures nodes(n, end);
{
    close nodes(n, end);
}

lemma void nodes_concat(*mut Node a, *mut Node b, *mut Node c)
    requires nodes(a, b) &*& nodes(b, c);
    ensures nodes(a, c);
{
    open nodes(a, b);
    if (a == b) {
    } else {
        nodes_concat(?next, b, c);
        close nodes(a, c);
    }
}

@*/

impl Node {
    #[requires(nodes(n, std::ptr::null_mut()))]
    #[ensures(nodes(result, std::ptr::null_mut()))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        /*@
        close nodes(m, std::ptr::null_mut());
        @*/
        loop {
            /*@
            invariant nodes(m, std::ptr::null_mut()) &*& nodes(n, std::ptr::null_mut());
            @*/
            if n.is_null() {
                /*@
                open nodes(n, std::ptr::null_mut());
                @*/
                return m;
            }
            /*@
            nodes_unfold_nonnull(n, std::ptr::null_mut());
            @*/
            let k = (*n).next;

            (*n).next = m;
            /*@
            nodes_fold_nonnull(n, std::ptr::null_mut(), m);
            nodes_concat(n, std::ptr::null_mut(), std::ptr::null_mut());
            @*/
            m = n;
            n = k;
        }
    }
}