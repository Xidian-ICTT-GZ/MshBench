struct Node {
    next: *mut Node,
}

predicate nodes(struct Node* n) = 
    n == 0 
        ? emp 
        : n->next |-> ?next &*& nodes(next);

impl Node {

    #[requires(nodes(n))]
    #[ensures(nodes(result))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node
    #[invariant(nodes(n) &*& nodes(m))] 
    {
        let mut m = std::ptr::null_mut();
        while (true)
            #[invariant(nodes(n) &*& nodes(m))]
        {
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