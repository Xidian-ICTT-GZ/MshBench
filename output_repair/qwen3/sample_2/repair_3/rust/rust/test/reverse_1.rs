struct Node {
    next: *mut Node,
}

predicate node(p: *mut Node, next: *mut Node) = (*p).next |-> next;

predicate nodes(p: *mut Node, xs: list<*mut Node>) =
    match xs {
        nil => p == std::ptr::null_mut(),
        cons(h, t) => exists q. node(p, q) * nodes(q, t)
    };

lemma void reverse_append<t>(xs: list<t>, ys: list<t>)
    requires true;
    ensures reverse(xs ++ ys) == reverse(ys) ++ reverse(xs);
{
    match xs {
        nil => (),
        cons(x, xs0) => {
            reverse_append(xs0, ys);
        }
    }
}

lemma void reverse_reverse<t>(xs: list<t>)
    requires true;
    ensures reverse(reverse(xs)) == xs;
{
    match xs {
        nil => (),
        cons(x, xs0) => {
            reverse_reverse(xs0);
            reverse_append(reverse(xs0), cons(x, nil));
        }
    }
}

impl Node {
    #[requires(nodes(n, xs))]
    #[ensures(nodes(result, reverse(xs)))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        proof_assert nodes(m, nil);
        #[invariant(exists ys. nodes(n, ys) * nodes(m, reverse(ys)) * xs == ys ++ reverse(reverse(ys)))]
        loop {
            if n.is_null() {
                return m;
            }
            let k = (*n).next;
            open nodes(n, _);
            let ys_rest = _;
            assert nodes(k, ys_rest);
            (*n).next = m;
            close node(n, m);
            close nodes(n, cons(n, ys_rest));
            m = n;
            n = k;
            reverse_reverse(ys_rest);
            reverse_append(cons(n, ys_rest), reverse(reverse(ys_rest)));
        }
    }
}