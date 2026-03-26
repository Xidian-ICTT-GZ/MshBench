use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred stack_pred(Stack *stack) = stack |-> Stack { head: ?head } &*& nodes_pred(head);
//@ pred nodes_pred(*mut Node n) = n == 0 ? true : n |-> Node { next: ?next, value: _ } &*& nodes_pred(next);

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack_pred(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        //@ close nodes_pred(std::ptr::null_mut());
        //@ close stack_pred(stack);

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
        //@ open stack_pred(stack);
        //@ open nodes_pred((*stack).head);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes_pred(n);
        //@ close stack_pred(stack);
    }
    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack_pred(stack);
    //@ ensures true;
    {
        //@ open stack_pred(stack);
        //@ open nodes_pred((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}