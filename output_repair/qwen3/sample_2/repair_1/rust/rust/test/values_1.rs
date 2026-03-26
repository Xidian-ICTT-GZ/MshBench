use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}
struct Stack {
    head: *mut Node,
}

predicate node_list(*mut Node head;);

predicate stack_inv(*mut Stack s) = 
    s |-> ?stack &*& node_list(stack.head);

predicate node_list(*mut Node head;) =
    match head {
        null => true,
        _ => head |-> ?node &*& node_list(node.next)
    };

impl Stack {
    #[ensures(result != null && stack_inv(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        leak stack |-> Stack { head: std::ptr::null_mut() };
        leak node_list(std::ptr::null_mut());
        stack
    }
    
    #[requires(stack != null &*& stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        close node_list(n);
        close stack_inv(stack);
    }
    
    #[requires(stack != null &*& stack_inv(stack))]
    unsafe fn dispose(stack: *mut Stack) {
        open stack_inv(stack);
        open node_list((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}