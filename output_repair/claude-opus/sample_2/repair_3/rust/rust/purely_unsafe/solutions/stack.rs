use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Node_own(node: *mut Node; next: *mut Node, value: i32) =
    (*node).next |-> next &*& (*node).value |-> value &*& alloc_block(node as *mut u8, Layout::new_::<Node>());

pred Nodes(head: *mut Node;) =
    if head == 0 {
        true
    } else {
        Node_own(head, ?next, ?value) &*& Nodes(next)
    };

pred Stack_own(stack: *mut Stack;) =
    (*stack).head |-> ?head &*& alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& Nodes(head);

@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack_own(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close Nodes(0 as *mut Node);
        (*stack).head = std::ptr::null_mut();
        //@ close Stack_own(stack);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack_own(stack);
    //@ ens Stack_own(stack);
    {
        //@ open Stack_own(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Node_own(n, (*stack).head, value);
        //@ close Nodes(n);
        (*stack).head = n;
        //@ close Stack_own(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack_own(stack) &*& (*stack).head != 0;
    //@ ens Stack_own(stack);
    {
        //@ open Stack_own(stack);
        let head = (*stack).head;
        //@ open Nodes(head);
        //@ open Node_own(head, _, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack_own(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack_own(stack) &*& (*stack).head == 0;
    //@ ens true;
    {
        //@ open Stack_own(stack);
        //@ open Nodes(0 as *mut Node);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}