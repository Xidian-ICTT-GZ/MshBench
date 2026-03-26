use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

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
        alloc_block_Node(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?value &*&
        Nodes(next)
    };

pred Stack(s: *mut Stack;) =
    alloc_block_Stack(s) &*&
    (*s).head |-> ?head &*&
    Nodes(head);

@*/

impl Stack {
    //@ req true;
    //@ ens result == 0 ? true : Stack(result);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close Nodes(0 as *mut Node);
        (*stack).head = std::ptr::null_mut();
        //@ close Stack(stack);

        stack
    }

    //@ req Stack(stack);
    //@ ens Stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
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

    //@ req Stack(stack) &*& (*stack).head |-> 0 as *mut Node;
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open Stack(stack);
        //@ open Nodes(0 as *mut Node);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}