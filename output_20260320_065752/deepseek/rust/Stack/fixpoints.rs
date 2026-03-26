use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred Node(node: *mut Node; next: *mut Node, value: i32) =
    alloc_block(node, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(node) &*&
    (*node).next |-> next &*&
    (*node).value |-> value;
@*/

struct Node {
    next: *mut Node,
    value: i32,
}

/*@
pred Stack(stack: *mut Stack; head: *mut Node) =
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> head;
@*/

struct Stack {
    head: *mut Node,
}

/*@
pred lseg(start: *mut Node, end: *mut Node) =
    start == end ?
        true
    :
        Node(start, ?next, ?value) &*& lseg(next, end);
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
    
    //@ req Stack(stack, ?head);
    //@ ens Stack(stack, ?new_head) &*& Node(new_head, head, value);
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open Stack(stack, head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Node(n, head, value);
        //@ close Stack(stack, n);
    }
    
    //@ req Stack(stack, ?head) &*& Node(head, ?next, ?value);
    //@ ens Stack(stack, next) &*& result == value;
    unsafe fn pop(stack: *mut Stack) -> i32 {
        //@ open Stack(stack, head);
        let head = (*stack).head;
        //@ open Node(head, next, value);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack, next);
        result
    }

    //@ req Stack(stack, std::ptr::null_mut());
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack) {
        //@ open Stack(stack, std::ptr::null_mut());
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);
        //@ assert result1 == 20;
        let result2 = Stack::pop(s);
        //@ assert result2 == 10;
        Stack::dispose(s);
    }
}