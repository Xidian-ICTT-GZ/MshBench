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
        v :: vs => node != std::ptr::null_mut() &*&
                   struct_Node(node) &*&
                   (*node).value |-> v &*&
                   (*node).next |-> ?next &*&
                   Nodes(next, vs)
    };

predicate Stack_own(*mut Stack stack; list<i32> values) =
    stack != std::ptr::null_mut() &*&
    struct_Stack(stack) &*&
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
    
    #[requires(Stack_own(stack, ?vs))]
    #[ensures(Stack_own(stack, [value] ++ vs))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }
    
    #[requires(Stack_own(stack, ?vs) &*& vs != [])]
    #[ensures(Stack_own(stack, tail(vs)) &*& result == head(vs))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(Stack_own(stack, []))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);
        let result2 = Stack::pop(s);
        Stack::dispose(s);
    }
}