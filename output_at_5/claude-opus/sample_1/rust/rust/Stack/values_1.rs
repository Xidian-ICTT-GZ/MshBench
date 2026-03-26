use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {
    //@ pred stack_pred(stack_ptr: *mut Stack) =
    //@     stack_ptr->head;

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack_pred(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack_pred(stack);
    //@ ensures stack_pred(stack);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack_pred(stack);
    //@ ensures true;
    {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}