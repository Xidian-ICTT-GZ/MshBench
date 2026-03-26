use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}
struct Stack {
    head: *mut Node,
}

/*@
pred Nodes(n: *mut Node;) =
    if n == 0 {
        true
    } else {
        (*n).next |-> ?next &*& (*n).value |-> ?v &*& struct_Node_padding(n) &*& alloc_block(n as *mut u8, Layout_new_Node_()) &*& Nodes(next)
    };

pred Stack(s: *mut Stack;) =
    (*s).head |-> ?head &*& struct_Stack_padding(s) &*& alloc_block(s as *mut u8, Layout_new_Stack_()) &*& Nodes(head);
@*/

impl Stack {
    /*@
    requires true;
    ensures result == 0 ? true : Stack(result);
    @*/
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close Nodes(0 as *mut Node);
        (*stack).head = std::ptr::null_mut();
        //@ close Stack(stack);
        stack
    }

    /*@
    requires Stack(stack);
    ensures Stack(stack);
    @*/
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open Stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Nodes(n);
        (*stack).head = n;
        //@ close Stack(stack);
    }

    /*@
    requires Stack(stack) &*& (*stack).head != 0;
    ensures Stack(stack);
    @*/
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

    /*@
    requires Stack(stack) &*& (*stack).head == 0;
    ensures true;
    @*/
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