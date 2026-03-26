struct Node {
    next: *mut Node,
}

predicate Nodes(*mut Node n;);

predicate Node(node: *mut Node, next: *mut Node) =
    node != std::ptr::null_mut() &*&
    struct_Node_padding(node) &*&
    struct_Node_next(node, next) &*&
    if next == std::ptr:: null_mut() {
        true
    } else {
        Nodes(next)
    };

predicate Nodes(*mut Node n;) =
    if n == std::ptr::null_mut() {
        true
    } else {
        exists(?next) &*& Node(n, next)
    };

lemma void Nodes_split(*mut Node n)
    requires Nodes(n);
    ensures n == std::ptr::null_mut() ? true : (exists(?next) &*& Node(n, next));
{
    open Nodes(n);
}

lemma void Nodes_join(*mut Node n)
    requires n == std::ptr::null_mut() ? true : (exists(?next) &*& Node(n, next));
    ensures Nodes(n);
{
    if n != std::ptr::null_mut() {
        close Nodes(n);
    }
}

impl Node {

    #[requires(Nodes(n))]
    #[ensures(Nodes(result))]
    unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
        let mut m = std::ptr::null_mut();
        loop {
            #[invariant(Nodes(n) &*& Nodes(m))]
            {
                if n.is_null() {
                    return m;
                }
                Nodes_split(n);
                let k = (*n).next;
                (*n).next = m;
                close Node(n, m);
                m = n;
                n = k;
            }
        }
    }

}