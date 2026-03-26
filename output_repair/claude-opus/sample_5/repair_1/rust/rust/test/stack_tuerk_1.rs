struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(n: *mut Node) =
    n.is_null() ? true : (
        exists next: *mut Node;
        (n as *mut Node) -> Node { next } &*& node_list(next)
    );

predicate stack(s: *mut Stack) =
    exists head: *mut Node;
    (s as *mut Stack) -> Stack { head } &*& node_list(head);

#[requires(stack(stack))]
#[ensures(result >= 0)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        #[invariant(i >= 0 &*& node_list(n))]
        {
            if n.is_null() {
                break;
            }
            n = (*n).next;
            i += 1;
        }
    }

    i
}