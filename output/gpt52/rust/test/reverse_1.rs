struct Node {
    next: *mut Node,
}

/*@

predicate nodes(struct Node *n; list<struct Node *> xs) =
    n == 0 ?
        xs == nil
    :
        n->next |-> ?next &*& nodes(next; ?xs0) &*& xs == cons(n, xs0);

lemma void nodes_nil()
    requires nodes(0; ?xs);
    ensures xs == nil;
{
    open nodes(0; xs);
}

lemma void nodes_nonnull(struct Node *n)
    requires nodes(n; ?xs) &*& n != 0;
    ensures n->next |-> ?next &*& nodes(next; ?xs0) &*& xs == cons(n, xs0);
{
    open nodes(n; xs);
}

lemma void nodes_rebuild(struct Node *n, struct Node *next)
    requires n->next |-> next &*& nodes(next; ?xs0);
    ensures nodes(n; cons(n, xs0));
{
    close nodes(n; cons(n, xs0));
}

lemma void nodes_append(struct Node *a)
    requires nodes(a; ?xs) &*& nodes(?b; ?ys) &*& xs != nil;
    ensures nodes(a; append(xs, ys));
{
    nodes_nonnull(a);
    nodes_append(?next);
    nodes_rebuild(a, next);
}

lemma void nodes_append_nil(struct Node *b)
    requires nodes(b; ?ys);
    ensures nodes(b; append(nil, ys)) &*& append(nil, ys) == ys;
{
}

@*/

impl Node {
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ requires nodes(n; ?xs);
    //@ ensures nodes(result; reverse(xs));
    {
        let mut m = std::ptr::null_mut();
        //@ close nodes(m; nil);
        //@ list<*mut Node> acc = nil;
        loop {
            /*@
            invariant nodes(n; ?rest) &*& nodes(m; ?acc0) &*& reverse(acc0) == acc &*& xs == append(reverse(acc), rest);
            @*/
            if n.is_null() {
                //@ nodes_nil();
                //@ assert rest == nil;
                //@ assert xs == append(reverse(acc), nil);
                //@ assert xs == reverse(acc);
                //@ assert reverse(xs) == reverse(reverse(acc));
                //@ assert reverse(reverse(acc)) == acc0;
                return m;
            }
            //@ nodes_nonnull(n);
            let k = (*n).next;

            (*n).next = m;
            //@ nodes_rebuild(n, m);
            //@ list<*mut Node> acc1 = cons(n, acc);
            //@ acc = acc1;
            m = n;
            n = k;
        }
    }
}