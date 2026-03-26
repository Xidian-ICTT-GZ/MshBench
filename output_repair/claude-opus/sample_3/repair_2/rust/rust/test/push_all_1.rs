use std::alloc::{dealloc, Layout};

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@
pred node_list(n: *mut Node) =
    if n == std::ptr::null_mut() {
        emp
    } else {
        (*n).next |-> ?next &*& node_list(next)
    };

pred stack_owns(s: *mut Stack) =
    (*s).head |-> ?head &*& node_list(head);
@*/

impl Stack {
    /*@
    req stack_owns(stack) &*& stack_owns(other);
    ens stack_owns(stack);
    @*/
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            /*@
            inv (*n).next |-> ?nxt &*& node_list(nxt) &*& stack_owns(stack);
            @*/
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