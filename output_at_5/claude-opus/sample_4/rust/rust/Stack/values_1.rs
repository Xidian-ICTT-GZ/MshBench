use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {
    /*@
    pred nodes(n: *mut Node) =
        n == std::ptr::null_mut()
        ? emp
        : n->next |-> ?next &*& n->value |-> _ &*& nodes(next);

    pred stack(stack_ptr: *mut Stack, head: *mut Node) =
        stack_ptr->head |-> head;
    @*/

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result, std::ptr::null_mut());
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack, ?head) &*& nodes(head);
    //@ ensures stack(stack, ?new_head) &*& nodes(new_head);
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
    //@ requires stack(stack, ?head) &*& nodes(head);
    //@ ensures true;
    {
        //@ open stack(stack, head);
        let mut current = head;
        while current != std::ptr::null_mut()
        //@ invariant nodes(current);
        {
            //@ open nodes(current);
            let next = (*current).next;
            dealloc(current as *mut u8, Layout::new::<Node>());
            current = next;
        }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}