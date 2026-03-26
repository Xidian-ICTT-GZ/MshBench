use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}
struct Stack {
    head: *mut Node,
}

predicate nodes_list(*const Node n) =
    n == std::ptr::null_mut() ?
        emp
    :
        n |-> Node { next: ?next, value: _ } &*&
        nodes_list(next);

predicate stack(*const Stack s) =
    s |-> Stack { head: ?head } &*&
    nodes_list(head);

impl Stack {
    #[requires(true)]
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
    {
        
        let mut n = (*stack).head;
        while n != std::ptr::null_mut()
            
            invariant nodes_list(n) &*&
                      stack(stack) &*&
                      (*stack).head == n;
        {
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}