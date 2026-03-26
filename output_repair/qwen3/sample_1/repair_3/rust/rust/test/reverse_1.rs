struct Node {
    next: *mut Node,
}

/*@

pred node(n: *mut Node, next: *mut Node) =
    n != 0 as *mut Node &*&
    (*n).next |-> next;

pred nodes(n: *mut Node; ns: list<*mut Node>) =
    match ns {
        cons(h, t) => node(n, h) * nodes(h, t),
        nil => n == 0 as *mut Node
    };

lemma void reverse_append<t>(list<t> xs, list<t> ys)
    requires true;
    ensures reverse(append(xs, ys)) == append(reverse(ys), reverse(xs));
{
    open append(xs, ys);
    match xs {
        cons(x, xs0) => {
            reverse_append(xs0, ys);
            close append(reverse(ys), reverse(xs));
        }
        nil => {
            close append(reverse(ys), reverse(xs));
        }
    }
}

@*/

impl Node {
    #[requires(nodes(n, nodes))]
    #[ensures(nodes(result, reverse(nodes)))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        #[invariant(nodes(n, xs) * nodes(m, ys) * eq(append(reverse(xs), ys), reverse(nodes)))]
        loop {
            if n.is_null() {
                return m;
            }
            let k = (*n).next;

            /*@
            assert node(n, ?next_val);
            @*/
            (*n).next = m;
            /*@
            close node(n, m);
            @*/
            m = n;
            n = k;
            /*@
            open nodes(old_n, ?old_xs);
            assert old_xs == cons(?h, ?t);
            assert xs == t;
            assert ys == cons(h, old_ys);
            reverse_append(t, cons(h, nil));
            @*/
        }
    }
}