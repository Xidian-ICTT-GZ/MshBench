use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate Nodes(node: *mut Node; values: list<i32>) =
    match values {
        cons(v, vs) => node != 0i32 as *mut Node && 
                       (*node).value |-> v &*& 
                       (*node).next |-> ?next &*& 
                       Nodes(next, vs),
        nil => node == 0i32 as *mut Node
    };

predicate Stack_own(stack: *mut Stack; values: list<i32>) =
    stack != 0i32 as *mut Stack &*&
    (*stack).head |-> ?head &*&
    Nodes(head, values);

impl Stack {
    #[requires(true)]
    #[ensures(Stack_own(result, nil))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(Stack_own(stack, ?old_values))]
    #[ensures(Stack_own(stack, cons(value, old_values)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(Stack_own(stack, _))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}