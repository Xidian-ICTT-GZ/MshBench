#![feature(stmt_expr_attributes)]

use std::alloc::{dealloc, Layout};

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[verifast::predicate]
fn node(n: *mut Node) -> bool {
    n != std::ptr::null_mut() && std::ptr::read(n).next as usize == std::ptr::read(n).next as usize
}

#[verifast::predicate]
fn stack(s: *mut Stack, head: *mut Node) -> bool {
    s != std::ptr::null_mut() &&
    (head == std::ptr::null_mut() ||
     node(head)) &&
    (*s).head == head
}

impl Stack {
    #[verifast::requires(other != std::ptr::null_mut())]
    #[verifast::requires(stack != std::ptr::null_mut())]
    #[verifast::requires(stack != other)]
    #[verifast::requires(forall(*p : *mut Node. node(p) ==>
        (*p).next == std::ptr::null_mut() || node((*p).next)))]
    #[verifast::requires(stack(stack, ?head1))]
    #[verifast::requires(stack(other, ?head2))]
    #[verifast::ensures(stack(stack, if head2 == std::ptr::null_mut() { head1 } else { head2 }))]
    #[verifast::ensures(verifast::dealloc_block(other as *mut u8, Layout::new::<Stack>()))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            verifast::invariant!(n != std::ptr::null_mut());
            verifast::invariant!(node(n));
            verifast::invariant!(forall(*p : *mut Node. node(p) ==>
                (*p).next == std::ptr::null_mut() || node((*p).next)));
            verifast::invariant!(stack(stack, head1));
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