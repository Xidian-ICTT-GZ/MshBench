#![feature(stmt_expr_attributes)]

use std::alloc::{dealloc, Layout};

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        (*n).next |-> ?next &*& node(next)
    }
}

#[predicate]
fn stack(s: *mut Stack, head: *mut Node) -> bool {
    if s.is_null() {
        true
    } else {
        (*s).head |-> head &*& node(head)
    }
}

impl Stack {
    #[requires(stack(stack, ?head1) &*& stack(other, ?head2))]
    #[ensures(stack(stack, head2) &*& stack(other, _))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            loop
                #[invariant(node(n) &*& n != std::ptr::null_mut())]
            {
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