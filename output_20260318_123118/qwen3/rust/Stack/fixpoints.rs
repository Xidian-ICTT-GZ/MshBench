use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate Nodes(node: *mut Node; values: list<i32>) =
    node == 0i32 as *mut Node ?
        values == []
    :
        node != 0i32 as *mut Node &*&
        alloc_block(node as *u8, Layout::new::<Node>()) &*&
        struct_Node_padding(node) &*&
        (*node).value |-> ?v &*&
        (*node).next |-> ?next &*&
        Nodes(next, ?rest) &*&
        values == cons(v, rest);

predicate Stack_own(stack: *mut Stack) =
    alloc_block(stack as *u8, Layout::new::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> ?head &*&
    Nodes(head, ?values);

impl Stack {

    #[requires(true)]
    #[ensures(Stack_own(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    #[requires(Stack_own(stack))]
    #[ensures(Stack_own(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }
    
    #[requires(Stack_own(stack))]
    #[ensures(Stack_own(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(Stack_own(stack))]
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