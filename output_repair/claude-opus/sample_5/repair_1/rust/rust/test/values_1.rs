use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}
struct Stack {
    head: *mut Node,
}

/*@
pred node_list(head: *mut Node) =
    if head == std::ptr::null_mut() {
        emp
    } else {
        (*head).next |-> ?next &*& (*head).value |-> ?_ &*& node_list(next)
    };

pred stack_inv(stack: *mut Stack) =
    (*stack).head |-> ?head &*& node_list(head);
@*/

impl Stack {
    #[requires(emp)]
    #[ensures(*result |-> ?s &*& stack_inv(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }
    #[requires(stack_inv(stack))]
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
    #[requires(stack_inv(stack))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}