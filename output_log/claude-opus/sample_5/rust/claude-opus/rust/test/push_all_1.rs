predicate Node(n: *mut Node, next: *mut Node) = 
    struct_Node_padding(n) &*& (*n).next |-> next;

predicate Nodes(n: *mut Node; last: *mut Node) =
    if n.is_null() {
        last == n
    } else {
        Node(n, ?next) &*& Nodes(next, last)
    };

predicate Stack(s: *mut Stack, head: *mut Node) =
    struct_Stack_padding(s) &*& (*s).head |-> head;

lemma fn nodes_last_not_null(n: *mut Node)
    requires Nodes(n, ?last) &*& n != std::ptr::null_mut();
    ensures Nodes(n, last) &*& last != std::ptr::null_mut();
{
    open Nodes(n, last);
    if (*n).next.is_null() {
        close Nodes(n, last);
    } else {
        nodes_last_not_null((*n).next);
        close Nodes(n, last);
    }
}

lemma fn nodes_append(n: *mut Node, tail: *mut Node)
    requires Nodes(n, ?last) &*& last != std::ptr::null_mut() &*& Node(last, std::ptr::null_mut()) &*& Nodes(tail, ?last2);
    ensures Nodes(n, last2) &*& Node(last, tail);
{
    open Nodes(n, last);
    if (*n).next.is_null() {
        close Nodes(tail, last2);
        close Nodes(n, last2);
    } else {
        nodes_append((*n).next, tail);
        close Nodes(n, last2);
    }
}

impl Stack {
    #[requires(Stack(stack, ?h1) &*& Stack(other, ?h2) &*& Nodes(h2, ?last2))]
    #[ensures(Stack(stack, ?h) &*& Nodes(h, _))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            #[invariant(Stack(stack, ?h) &*& Nodes(head0, ?last) &*& 
                        (n == head0 ? true : Nodes(head0, n)) &*& 
                        (n == last ? true : (Node(n, ?nx) &*& Nodes(nx, last))))]
            loop {
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
            }

            // At this point, Nodes(head0, last) with last == n holds,
            // and Node(last, null) with last == n holds, so safe to append.
            nodes_append(head0, (*stack).head);

            (*stack).head = head0;
        }
    }
}