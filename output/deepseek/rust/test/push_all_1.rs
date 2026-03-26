use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_own(n: *mut Node, v: i32, next: *mut Node) -> bool {
    unsafe { (*n).value == v && (*n).next == next }
}

#[predicate]
fn nodes(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        exists!(v: i32, next: *mut Node => 
            node_own(n, v, next) * nodes(next))
    }
}

#[predicate]
fn stack_own(s: *mut Stack) -> bool {
    unsafe { exists!(head: *mut Node => 
        (*s).head == head && nodes(head)) }
}

impl Stack {
    #[requires(stack_own(stack))]
    #[requires(stack_own(other))]
    #[ensures(stack_own(stack))]
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