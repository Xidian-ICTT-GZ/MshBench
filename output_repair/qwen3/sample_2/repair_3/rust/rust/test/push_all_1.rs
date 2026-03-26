#![feature(stmt_expr_attributes)]

use std::alloc::{dealloc, Layout};

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node(*mut Node n; *mut Node next) =
    n == null ? true :
    n |-> ?n_next &*& node(n_next, ?nn_next) &*& next == n_next;

predicate stack(*mut Stack s; *mut Node head) =
    s == null ? true :
    s |-> ?s_head &*& node(s_head, ?h) &*& head == s_head;

unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    requires stack(stack, ?head1) &*& stack(other, ?head2);
    ensures stack(stack, head2) &*& stack(other, _);
{
    let head0 = (*other).head;
    dealloc(other as *mut u8, Layout::new::<Stack>());
    let mut n = head0;

    if n != null {
        loop
            invariant node(n, ?tail) &*& tail == null &*& n != null;
        {
            if (*n).next == null {
                break;
            }
            n = (*n).next;
        }

        (*n).next = (*stack).head;
        (*stack).head = head0;
    }
}