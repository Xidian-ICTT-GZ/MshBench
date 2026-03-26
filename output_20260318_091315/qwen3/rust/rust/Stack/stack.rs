use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate Nodes(*mut Node node; i32 v, *mut Node next) =
    node != std::ptr::null_mut() &*&
    struct_Node_padding(node) &*&
    struct_Node_next(node, next) &*&
    struct_Node_value(node, v);

predicate Stack_own(*mut Stack stack; list<i32> values) =
    stack != std::ptr::null_mut() &*&
    struct_Stack_padding(stack) &*&
    struct_Stack_head(stack, ?head) &*&
    Stack_nodes(head, values);

predicate Stack_nodes(*mut Node node; list<i32> values) =
    match values {
        cons(v, vs) => Nodes(node, v, ?next) &*& Stack_nodes(next, vs),
        nil => node == std::ptr::null_mut()
    };

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

    #[requires(Stack_own(stack, ?vs))]
    #[ensures(Stack_own(stack, cons(value, vs)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(Stack_own(stack, cons(?v, ?vs)))]
    #[ensures(Stack_own(stack, vs) &*& result == v)]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(Stack_own(stack, _))]
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
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}