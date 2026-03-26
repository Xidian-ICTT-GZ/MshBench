use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Node(node: *mut Node; next: *mut Node, value: i32) =
    alloc_block(node, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(node) &*&
    (*node).next |-> next &*&
    (*node).value |-> value;
@*/

/*@
pred Stack(stack: *mut Stack; head: *mut Node) =
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> head;
@*/

impl Stack {
    //@ req true;
    //@ ens Stack(result, std::ptr::null_mut());
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Stack(stack, std::ptr::null_mut());
        stack
    }
    
    //@ req Stack(stack, head);
    //@ ens Stack(stack, n) &*& Node(n, head, value);
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open Stack(stack, head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Node(n, (*n).next, value);
        //@ close Stack(stack, n);
    }

    //@ req Stack(stack, _);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack) {
        //@ open Stack(stack, _);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}