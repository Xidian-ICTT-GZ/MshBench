use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Node_own(n: *mut Node; next: *mut Node, value: i32) =(*n).next |-> next &*& (*n).value |-> value &*& alloc_block(n as *mut u8, Layout::new_::<Node>());

pred Nodes(n: *mut Node;) =
    if n == 0 as *mut Node {
        true
    } else {
        Node_own(n, ?next, ?value) &*& Nodes(next)
    };

pred Stack_own(s: *mut Stack; head: *mut Node) =
    (*s).head |-> head &*& alloc_block(s as *mut u8, Layout::new_::<Stack>());

pred Stack(s: *mut Stack;) =
    Stack_own(s, ?head) &*& Nodes(head);

@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req Nodes(nodes);
//@ ens Nodes(nodes);
{
    let mut result = 0;

    if !nodes.is_null() {
        //@ open Nodes(nodes);
        //@ open Node_own(nodes, ?next, ?value);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close Node_own(nodes, next, value);
        //@ close Nodes(nodes);
    }

    result
}

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
        //@ close Stack_own(stack, 0 as *mut Node);
        //@ close Stack(stack);
        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req Stack(stack);
    //@ ens Stack(stack);
    {
        //@ open Stack(stack);
        //@ open Stack_own(stack, ?head);
        let head = (*stack).head;

        let result = (*stack).head.is_null();
        //@ close Stack_own(stack, head);
        //@ close Stack(stack);
        result
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req Stack(stack);
    //@ ens Stack(stack);
    {
        //@ open Stack(stack);
        //@ open Stack_own(stack, ?head);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack_own(stack, head);
        //@ close Stack(stack);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack(stack);
    //@ ens Stack(stack);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open Stack(stack);
        //@ open Stack_own(stack, ?old_head);
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Node_own(n, old_head, value);
        //@ close Nodes(n);
        (*stack).head = n;
        //@ close Stack_own(stack, n);
        //@ close Stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack(stack) &*& (*stack).head != 0 as *mut Node;
    //@ ens Stack(stack);
    {
        //@ open Stack(stack);
        //@ open Stack_own(stack, ?head);
        let head = (*stack).head;
        //@ open Nodes(head);
        //@ open Node_own(head, ?next, ?val);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack_own(stack, next);
        //@ close Stack(stack);
        result
    }

    unsafe fn popn(stack: *mut Stack, n: i32)
    //@ req Stack(stack) &*& n >= 0;
    //@ ens Stack(stack);
    {
        let mut i = 0;
        loop
        //@ inv Stack(stack) &*& i >= 0 &*& i <= n;
        {
            if i == n {
                break;
            }
            //@ open Stack(stack);
            //@ open Stack_own(stack, ?head);
            //@ open Nodes(head);
            //@ open Node_own(head, ?next, ?val);
            let head = (*stack).head;
            let result = (*head).value;
            (*stack).head = (*head).next;
            dealloc(head as *mut u8, Layout::new::<Node>());
            //@ close Stack_own(stack, next);
            //@ close Stack(stack);
            i += 1;
        }}

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack);
    //@ ens true;
    {
        //@ open Stack(stack);
        //@ open Stack_own(stack, ?head);
        let mut n = (*stack).head;
        loop
        //@ inv Nodes(n) &*& alloc_block(stack as *mut u8, Layout::new_::<Stack>());
        {
            if n.is_null() {
                //@ open Nodes(n);
                break;
            }
            //@ open Nodes(n);
            //@ open Node_own(n, ?next, ?val);
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }

        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        //@ open Stack(s);
        //@ open Stack_own(s, ?h1);
        //@ open Nodes(h1);
        //@ open Node_own(h1, ?h2, _);
        //@ close Node_own(h1, h2, _);
        //@ close Nodes(h1);
        //@ close Stack_own(s, h1);
        //@ close Stack(s);
        Stack::pop(s);
        //@ open Stack(s);
        //@ open Stack_own(s, ?h3);
        //@ open Nodes(h3);
        //@ open Node_own(h3, ?h4, _);
        //@ close Node_own(h3, h4, _);
        //@ close Nodes(h3);
        //@ close Stack_own(s, h3);
        //@ close Stack(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}