struct Node {
    next: *mut Node,
}

predicate nodes(struct Node* n; ) = 
    n == 0 ? emp : 
    n->next |-> ?nx &*& nodes(nx);

impl Node {

    #[requires(nodes(n))]
    #[ensures(nodes(result))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    {
        #[predicate]
        fn loop_inv(struct Node* n, struct Node* m)
            requires nodes(n) &*& nodes(m);
            ensures nodes(n) &*& nodes(m);
        {
            n == 0 ?
                nodes(m) :
                nodes(m) &*& nodes(n);
        }

        let mut m = std::ptr::null_mut();
        #[invariant(loop_inv(n, m))]
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