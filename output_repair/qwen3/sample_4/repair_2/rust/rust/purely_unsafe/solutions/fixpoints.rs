use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Node(node: *mut Node; next: *mut Node, value: i32) =
    std::alloc::alloc_block(node as *mut u8, std::alloc::Layout::new::<Node>()) &*&
    (*node).next |-> next &*&
    (*node).value |-> value;

pred Nodes(node: *mut Node;) =
    if node == 0 {
        true
    } else {
        Node(node, ?next, ?value) &*& Nodes(next)
    };

pred Stack(stack: *mut Stack;) =
    std::alloc::alloc_block(stack as *mut u8, std::alloc::Layout::new::<Stack>()) &*&
    (*stack).head |-> ?head &*&
    Nodes(head);

pred Stack_nonempty(stack: *mut Stack;) =
    std::alloc::alloc_block(stack as *mut u8, std::alloc::Layout::new::<Stack>()) &*&
    (*stack).head |-> ?head &*&
    head != 0 &*&
    Node(head, ?next, ?value) &*&
    Nodes(next);

@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0 as *mut Node);
        //@ close Stack(stack);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack(stack);
    //@ ens Stack(stack);
    {
        //@ open Stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Node(n, (*stack).head, value);
        (*stack).head = n;
        //@ close Nodes(n);
        //@ close Stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack_nonempty(stack);
    //@ ens Stack(stack);
    {
        //@ open Stack_nonempty(stack);
        let head = (*stack).head;
        //@ open Node(head, ?next, ?value);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Nodes((*stack).head);
        //@ close Stack(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack);
    //@ ens true;
    {
        //@ open Stack(stack);
        //@ open Nodes((*stack).head);
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
        //@ open Stack(s);
        //@ open Nodes((*s).head);
        //@ assert (*s).head != 0;
        //@ close Stack_nonempty(s);
        let result1 = Stack::pop(s);
        //@ open Stack(s);
        //@ open Nodes((*s).head);
        //@ if ((*s).head != 0) { close Stack_nonempty(s); }
        let result2 = Stack::pop(s);

        Stack::dispose(s);
    }
}