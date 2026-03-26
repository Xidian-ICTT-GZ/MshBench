use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node_own(n: *mut Node) = 
    n != std::ptr::null_mut() && 
    Owned(n) && 
    Owned((*n).next);

predicate stack_own(s: *mut Stack) = 
    s != std::ptr::null_mut() && 
    Owned(s) && 
    Owned((*s).head);

predicate stack_list(s: *mut Stack) = 
    stack_own(s);

impl Stack {
    #[requires(true)]
    #[ensures(stack_list(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack_list(stack))]
    #[ensures(stack_list(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_list(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}