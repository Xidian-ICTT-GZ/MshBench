use std::alloc::{dealloc, Layout};

struct Node {
    data: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn nodes(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        let node = unsafe { &*n };
        nodes(node.next)
    }
}

#[predicate]
fn stack_nodes(s: *mut Stack) -> bool {
    if s.is_null() {
        false
    } else {
        let stack = unsafe { &*s };
        nodes(stack.head)
    }
}

#[predicate]
fn full_stack(s: *mut Stack) -> bool {
    stack_nodes(s)
}

impl Stack {
    #[requires(full_stack(stack))]
    #[requires(full_stack(other))]
    #[ensures(full_stack(stack))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            #[invariant(nodes(n))]
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