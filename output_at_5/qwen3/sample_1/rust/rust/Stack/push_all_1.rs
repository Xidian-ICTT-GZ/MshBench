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
        //@ requires (*other).head == heap_list(other, other_head);
        //@ requires valid_stack_ptr(other);
        //@ ensures (*stack).head == old((*stack).head) ++ other_head;
        //@ ensures valid_stack_ptr(stack);
        //@ ghost predicate heap_list(ptr: *mut Node, list: *mut Node) = true;
        //@ ghost predicate valid_stack_ptr(p: *mut Stack) = true;
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