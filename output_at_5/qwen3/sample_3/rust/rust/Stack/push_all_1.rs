use std::alloc::{dealloc, Layout};

struct Stack {
    head: *mut Node,
}

struct Node {
    next: *mut Node,
}

impl Stack {
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
        //@ requires stack != null;
        //@ requires other != null;
        //@ ghost predicate valid_stack_ptr(p: *mut Stack) = true;
        //@ ghost predicate valid_node_list(ptr: *mut Node) = true;
        //@ requires valid_stack_ptr(other);
        //@ ensures valid_stack_ptr(stack);
    {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
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