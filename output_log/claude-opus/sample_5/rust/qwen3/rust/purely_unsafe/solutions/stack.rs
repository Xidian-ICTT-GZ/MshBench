use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
pub struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
pub struct Stack {
    head: *mut Node,
}

predicate node_pred(n: *mut Node, value: i32, next: *mut Node) = 
    n->Node { next: next, value: value };

predicate stack_pred(s: *mut Stack, head: *mut Node) =
    s->Stack { head: head } &*& nodes_segment(head);

predicate nodes_segment(current: *mut Node) =
    if current == std::ptr::null_mut() {
        emp
    } else
        exists<int v, *mut Node next>(
            node_pred(current, v, next) &*& nodes_segment(next)
        );

impl Stack {
    #[trusted]
    #[requires(true)]
    #[ensures(result != std::ptr::null_mut() &*& stack_pred(result, std::ptr::null_mut()))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(stack_pred(stack, old_head))]
    #[ensures(stack_pred(stack, ?new_head) &*& new_head != std::ptr::null_mut() &*&
              node_pred(new_head, value, old_head))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        // Allocate node predicate for the new node
        // We do not expose n before initialization, so no ownership leak
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_pred(stack, head) &*& head != std::ptr::null_mut() &*& node_pred(head, ?v, ?next))]
    #[ensures(result == v &*& stack_pred(stack, next) &*& nodes_segment(next))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(stack_pred(stack, std::ptr::null_mut()))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}