struct Node {
    next: *mut Node,
}

/*@

pred nodes(struct Node *n; list<struct Node *> xs) =
    n == 0 ?
        xs == nil
    :
        n->next |-> ?next &*& nodes(next; ?xs0) &*& xs == cons(n, xs0);

@*/

impl Node {

    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ req nodes(n; ?xs);
    //@ ens nodes(result; reverse(xs));
    {
        //@ open nodes(n; xs);
        let mut m = std::ptr::null_mut();
        //@ close nodes(m; nil);
        loop {
            //@ inv nodes(n; ?xs1) &*& nodes(m; ?ys1) &*& append(reverse(ys1), xs1) == xs;
            if n.is_null() {
                //@ assert xs1 == nil;
                //@ assert append(reverse(ys1), nil) == xs;
                //@ assert reverse(ys1) == xs;
                //@ close nodes(n; nil);
                return m;
            }
            //@ open nodes(n; xs1);
            let k = (*n).next;
            (*n).next = m;
            //@ close nodes(n; cons(n, ys1));
            m = n;
            n = k;
        }
    }

}