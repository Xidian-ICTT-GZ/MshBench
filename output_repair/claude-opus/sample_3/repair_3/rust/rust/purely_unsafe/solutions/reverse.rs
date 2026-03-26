use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Node_own(n: *mut Node; next: *mut Node, value: i32) =
    alloc_block(n as *mut u8, Layout::new_::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;

pred Nodes(n: *mut Node;) =
    if n == 0 as *mut Node {
        true
    } else {
        Node_own(n, ?next, ?value) &*& Nodes(next)
    };

pred Stack_own(s: *mut Stack; head: *mut Node) =
    alloc_block(s as *mut u8, Layout::new_::<Stack>()) &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> head;

pred Stack_full(s: *mut Stack;) =
    Stack_own(s, ?head) &*& Nodes(head);
@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack_full(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close Nodes(0 as *mut Node);
        (*stack).head = std::ptr::null_mut();
        //@ close Stack_own(stack, 0 as *mut Node);
        //@ close Stack_full(stack);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack_full(stack);
    //@ ens Stack_full(stack);
    {
        //@ open Stack_full(stack);
        //@ open Stack_own(stack, ?old_head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Node_own(n, old_head, value);
        //@ close Nodes(n);
        (*stack).head = n;
        //@ close Stack_own(stack, n);
        //@ close Stack_full(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack_full(stack) &*& (*stack).head |-> ?h &*& h != 0 as *mut Node;
    //@ ens Stack_full(stack);
    {
        //@ open Stack_full(stack);
        //@ open Stack_own(stack, ?old_head);
        let head = (*stack).head;
        //@ open Nodes(head);
        //@ open Node_own(head, ?next, ?val);

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack_own(stack, next);
        //@ close Stack_full(stack);
        result
    }

    unsafe fn reverse(stack: *mut Stack)
    //@ req Stack_full(stack);
    //@ ens Stack_full(stack);
    {
        //@ open Stack_full(stack);
        //@ open Stack_own(stack, ?old_head);
        let mut n = (*stack).head;
        let mut m: *mut Node = std::ptr::null_mut();
        //@ close Nodes(m);

        loop
        //@ inv Nodes(n) &*& Nodes(m) &*& Stack_own(stack, _);
        {
            //@ open Nodes(n);
            if n.is_null() {
                //@ close Nodes(n);
                break;
            }
            //@ open Node_own(n, ?next_n, ?val_n);

            let next = (*n).next;

            (*n).next = m;
            //@ close Node_own(n, m, val_n);
            //@ close Nodes(n);
            m = n;
            n = next;
        }
        //@ open Stack_own(stack, _);
        (*stack).head = m;
        //@ close Stack_own(stack, m);
        //@ close Stack_full(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack_own(stack, 0 as *mut Node) &*& Nodes(0 as *mut Node);
    //@ ens true;
    {
        //@ open Stack_own(stack, 0 as *mut Node);
        //@ open Nodes(0 as *mut Node);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        //@ open Stack_full(s);
        //@ open Stack_own(s, ?h1);
        //@ close Stack_own(s, h1);
        //@ close Stack_full(s);
        let _result1 = Stack::pop(s);

        //@ open Stack_full(s);
        //@ open Stack_own(s, ?h2);
        //@ close Stack_own(s, h2);
        //@ close Stack_full(s);
        let _result2 = Stack::pop(s);

        //@ open Stack_full(s);
        Stack::dispose(s);
    }
}