struct Node {
    next: *mut Node,
}

/*@
pred Nodes(n: *mut Node; nodes: list<*mut Node>) =
    if n == 0 {
        nodes == nil
    } else {
        (*n).next |-> ?next &*& Nodes(next, ?rest) &*& nodes == cons(n, rest)
    };
@*/

impl Node {
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    //@ req Nodes(n, ?ns);
    //@ ens Nodes(result, ?ms) &*& reverse(ns) == ms;
    {
        let mut m: *mut Node = std::ptr::null_mut();
        //@ close Nodes(m, nil);
        loop {
            //@ inv Nodes(n, ?ns1) &*& Nodes(m, ?ms1) &*& reverse(ns) == append(reverse(ns1), ms1);
            if n.is_null() {
                //@ open Nodes(n, ns1);
                //@ append_nil(reverse(ns1));
                return m;
            }
            //@ open Nodes(n, ns1);
            let k = (*n).next;

            (*n).next = m;
            //@ close Nodes(n, cons(n, ms1));
            //@ reverse_cons_append(ns1);
            m = n;
            n = k;
        }
    }
}

/*@
lem append_nil<t>(xs: list<t>)
    req true;
    ens append(xs, nil) == xs;
{
    match xs {
        nil => {}
        cons(h, t) => { append_nil(t); }
    }
}

lem reverse_cons_append<t>(xs: list<t>)
    req xs != nil;
    ens reverse(xs) == append(reverse(tail(xs)), cons(head(xs), nil));
{
    match xs {
        nil => {}
        cons(h, t) => {}
    }
}
@*/