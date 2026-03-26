use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate Nodes(*mut Node node; list<i32> values) =
    match values {
        [] => node == std::ptr::null_mut(),
        ?v :: ?vs => 
            node != std::ptr::null_mut() &*&
            struct_Node_padding(node) &*&
            (*node).value |-> v &*&
            (*node).next |-> ?next &*&
            Nodes(next, vs)
    };

predicate Stack_own(*mut Stack stack; list<i32> values) =
    stack != std::ptr::null_mut() &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> ?head &*&
    Nodes(head, values);

impl Stack {

    #[requires(true)]
    #[ensures(Stack_own(result, []))]
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
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}