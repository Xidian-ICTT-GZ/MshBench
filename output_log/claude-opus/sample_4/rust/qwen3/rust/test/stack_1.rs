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
    (*n).next |-> next &*& (*n).value |-> value;

pred Nodes(head: *mut Node;) =
    if head == 0 {
        true
    } else {
        alloc_block(head as *mut u8, Layout::new_::<Node>()) &*&
        struct_Node_padding(head) &*&
        Node_own(head, ?next, ?value) &*&
        Nodes(next)
    };

pred Stack_own(s: *mut Stack; head: *mut Node) =
    (*s).head |-> head;
@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens alloc_block(result as *mut u8, Layout::new_::<Stack>()) &*& struct_Stack_padding(result) &*& Stack_own(result, 0 as *mut Node);
    {
        let layout = Layout::new::<Stack>();
        let stack = alloc(layout) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(layout);
        }
        //@ close_struct(stack);
        (*stack).head = std::ptr::null_mut();
        //@ close Stack_own(stack, 0 as *mut Node);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& struct_Stack_padding(stack) &*& Stack_own(stack, ?head) &*& Nodes(head);
    //@ ens alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& struct_Stack_padding(stack) &*& Stack_own(stack, ?new_head) &*& Nodes(new_head);
    {
        //@ open Stack_own(stack, head);
        let layout = Layout::new::<Node>();
        let n = alloc(layout) as *mut Node;
        if n.is_null() {
            handle_alloc_error(layout);
        }
        //@ close_struct(n);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Node_own(n, head, value);
        //@ close Nodes(n);
        //@ close Stack_own(stack, n);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& struct_Stack_padding(stack) &*& Stack_own(stack, ?head) &*& head != 0 as *mut Node &*& Nodes(head);
    //@ ens alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& struct_Stack_padding(stack) &*& Stack_own(stack, ?new_head) &*& Nodes(new_head);
    {
        //@ open Stack_own(stack, head);
        //@ open Nodes(head);
        //@ open Node_own(head, ?next, ?val);
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open_struct(head);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack_own(stack, next);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& struct_Stack_padding(stack) &*& Stack_own(stack, ?head) &*& Nodes(head);
    //@ ens true;
    {
        //@ open Stack_own(stack, head);
        let mut current = (*stack).head;
        loop {
            //@ inv Nodes(current);
            if current.is_null() {
                break;
            }
            //@ open Nodes(current);
            //@ open Node_own(current, ?next, ?val);
            let next = (*current).next;
            //@ open_struct(current);
            dealloc(current as *mut u8, Layout::new::<Node>());
            current = next;
        }
        //@ open Nodes(current);
        //@ open_struct(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        //@ close Nodes(0 as *mut Node);
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}