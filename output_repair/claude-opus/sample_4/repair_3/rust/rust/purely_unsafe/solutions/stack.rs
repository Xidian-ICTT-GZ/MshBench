use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Nodes(node: *mut Node;) =
    if node == 0 {
        true
    } else {
        (*node).next |-> ?next &*& (*node).value |-> ?value &*& struct_Node_padding(node) &*& alloc_block(node as *mut u8, Layout::new_::<Node>()) &*& Nodes(next)
    };

pred Stack(stack: *mut Stack;) =
    (*stack).head |-> ?head &*& struct_Stack_padding(stack) &*& alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& Nodes(head);

@*/

impl Stack {
    #[requires(true)]
    #[ensures(Stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0 as *mut Node);
        //@ close Stack(stack);
        stack
    }

    #[requires(Stack(stack))]
    #[ensures(Stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open Stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open Nodes((*stack).head);
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Nodes(n);
        (*stack).head = n;
        //@ close Stack(stack);
    }

    #[requires(Stack(stack))]
    #[ensures(Stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        //@ open Stack(stack);
        let head = (*stack).head;
        //@ open Nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack);
        result
    }

    #[requires(Stack(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        //@ open Stack(stack);
        //@ open Nodes(0 as *mut Node);
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