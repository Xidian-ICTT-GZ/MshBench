use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}
struct Stack {
    head: *mut Node,
}

predicate nodes(struct Node* n) = 
    n == std::ptr::null_mut() ?
    emp
    :
    n |-> Node { next: ?next, value: ?v } &*& nodes(next);

predicate stack(struct Stack* s, list<int> vs) = 
    s |-> Stack { head: ?h } &*& nodes(h) &*& nodes_values(h, vs);

predicate nodes_values(struct Node* n, list<int> vs) = 
    n == std::ptr::null_mut() ?
    vs == nil ? emp : false
    :
    n |-> Node { next: ?next, value: ?v } &*& nodes_values(next, ?rest) &*& vs == cons(v, rest);

impl Stack {
    #[requires(true)]
    #[ensures(stack(result, nil))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(stack(stack, cons(value, vs)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        open stack(stack, ?vs);
        open nodes((*stack).head);
        
        unsafe fn free_nodes(n: *mut Node)
            #[requires(nodes(n))]
            #[ensures(emp)]
        {
            if n != std::ptr::null_mut() {
                open nodes(n);
                let next = (*n).next;
                dealloc(n as *mut u8, Layout::new::<Node>());
                free_nodes(next);
            }
        }
        free_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}