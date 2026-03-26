use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}
struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_list(head: *mut Node) -> bool {
    match head {
        p if p.is_null() => true,
        p => {
            let n = unsafe { &*p };
            node_list(n.next)
        }
    }
}

#[predicate]
fn stack_inv(stack: *mut Stack) -> bool {
    let s = unsafe { &*stack };
    node_list(s.head)
}

impl Stack {
    #[ensures(result != std::ptr::null_mut() && stack_inv(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }
    
    #[requires(stack != std::ptr::null_mut() && stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }
    
    #[requires(stack != std::ptr::null_mut() && stack_inv(stack))]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}