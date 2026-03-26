#[predicate]
fn node(n: *mut Node) -> bool {
    n != std::ptr::null_mut() && (*n).next as usize == (*n).next as usize
}

#[predicate]
fn stack(s: *mut Stack, head: *mut Node) -> bool {
    s != std::ptr::null_mut() &&
    (head == std::ptr::null_mut() ||
     node(head)) &&
    (*s).head == head
}

impl Stack {
    #[requires(other != std::ptr::null_mut())]
    #[requires(stack != std::ptr::null_mut())]
    #[requires(stack != other)]
    #[requires(forall(*p : *mut Node. node(p) ==>
        (*p).next == std::ptr::null_mut() || node((*p).next)))]
    #[requires(stack(stack, ?head1))]
    #[requires(stack(other, ?head2))]
    #[ensures(stack(stack, if head2 == std::ptr::null_mut() { head1 } else { head2 }))]
    #[ensures(dealloc_block(other as *mut u8, Layout::new::<Stack>()))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            #[invariant(n != std::ptr::null_mut())]
            #[invariant(node(n))]
            #[invariant(forall(*p : *mut Node. node(p) ==>
                (*p).next == std::ptr::null_mut() || node((*p).next)))]
            #[invariant(stack(stack, head1))]
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


#![feature(stmt_expr_attributes)]

use std::alloc::{dealloc, Layout};

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}