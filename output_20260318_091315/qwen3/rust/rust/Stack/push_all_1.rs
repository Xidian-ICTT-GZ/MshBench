use std::alloc::{dealloc, Layout};

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate Nodes(node: *mut Node; nodes: list<*mut Node>) =
    match nodes {
        Nil => node == std::ptr::null_mut(),
        Cons(hd, tl) => node == hd && (*node).next |-> ?next &*& Nodes(next, tl),
    };

predicate Stack_own(s: *mut Stack; nodes: list<*mut Node>) =
    s |-> ?stack &*& stack.head |-> ?head &*& Nodes(head, nodes);

impl Stack {
    #[requires(Stack_own(other, ?nodes_other) &*& Stack_own(stack, ?nodes_stack))]
    #[ensures(Stack_own(stack, append(nodes_other, nodes_stack)))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            #[invariant(n |-> ?curr &*& Nodes(curr.next, ?suffix) &*& Stack_own(stack, ?nodes_stack) &*& curr != std::ptr::null_mut())]
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