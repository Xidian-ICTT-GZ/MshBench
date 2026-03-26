use std::alloc::{dealloc, Layout};

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate Nodes(*Node n, list<*Node> nodes) =
    if n == std::ptr::null_mut() {
        nodes == []
    } else {
        struct_Node_padding(n) &*& n |-> ?next &*& Nodes(next, ?tail) &*& nodes == cons(n, tail)
    };

predicate Stack_own(*mut Stack s, list<*Node> nodes) =
    struct_Stack_padding(s) &*& s |-> ?head &*& Nodes(head, nodes);

impl Stack {
    #[requires(Stack_own(stack, ?nodes1) &*& Stack_own(other, ?nodes2))]
    #[ensures(Stack_own(stack, append(nodes2, nodes1)))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            #[invariant(Nodes(n, ?curr_nodes) &*& Stack_own(stack, ?stack_nodes) &*& append(curr_nodes, stack_nodes) == append(nodes2, nodes1))]
            loop {
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
            }

            (*n).next = (*stack).head;

            (*stack).head = head0;
        }
    }
}