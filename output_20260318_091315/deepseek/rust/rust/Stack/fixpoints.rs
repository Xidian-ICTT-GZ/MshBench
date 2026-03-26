use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node(n: *mut Node, next: *mut Node, value: i32) -> bool {
    unsafe {
        (*n).next == next && (*n).value == value
    }
}

#[predicate]
fn nodes(head: *mut Node) -> bool {
    if head.is_null() {
        true
    } else {
        let next = unsafe { (*head).next };
        let value = unsafe { (*head).value };
        node(head, next, value) && nodes(next)
    }
}

#[predicate]
fn stack(s: *mut Stack) -> bool {
    unsafe {
        let head = (*s).head;
        nodes(head)
    }
}

impl Stack {
    #[requires(true)]
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        let old_head = (*stack).head;
        (*n).next = old_head;
        (*n).value = value;
        (*stack).head = n;
    }
    
    #[requires(stack(stack) && !(*stack).head.is_null())]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(stack(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);
        let result2 = Stack::pop(s);
        Stack::dispose(s);
    }
}