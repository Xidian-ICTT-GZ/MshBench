use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Node_own(p: *mut Node; next: *mut Node, value: i32) =
    (*p).next |-> next &*& (*p).value |-> value &*& struct_Node_padding(p);

pred Nodes(head: *mut Node;) =
    if head == std::ptr::null_mut() {
        true
    } else {
        Node_own(head, ?next, ?value) &*& alloc_block(head as *mut u8, Layout::new_::<Node>()) &*& Nodes(next)
    };

pred Stack_own(p: *mut Stack; head: *mut Node) =
    (*p).head |-> head &*& struct_Stack_padding(p);
@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack_own(result, std::ptr::null_mut()) &*& alloc_block(result as *mut u8, Layout::new_::<Stack>());
    {
        let layout = Layout::new::<Stack>();
        let stack = alloc(layout) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(layout);
        }
        //@ close_struct(stack);
        (*stack).head = std::ptr::null_mut();
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack_own(stack, ?head) &*& alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& Nodes(head);
    //@ ens Stack_own(stack, ?new_head) &*& alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& Nodes(new_head);
    {
        let layout = Layout::new::<Node>();
        let n = alloc(layout) as *mut Node;
        if n.is_null() {
            handle_alloc_error(layout);
        }
        //@ close_struct(n);
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Nodes(n);
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack_own(stack, ?head) &*& alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& Nodes(head) &*& head != std::ptr::null_mut();
    //@ ens Stack_own(stack, ?new_head) &*& alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& Nodes(new_head);
    {
        //@ open Nodes(head);
        let n = (*stack).head;
        let result = (*n).value;
        (*stack).head = (*n).next;
        //@ open_struct(n);
        dealloc(n as *mut u8, Layout::new::<Node>());
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack_own(stack, ?head) &*& alloc_block(stack as *mut u8, Layout::new_::<Stack>()) &*& Nodes(head);
    //@ ens true;
    {
        let mut current = (*stack).head;
        //@ close Nodes(current);
        loop {
            //@ inv Nodes(current);
            if current.is_null() {
                break;
            }
            //@ open Nodes(current);
            let next = (*current).next;
            //@ open_struct(current);
            dealloc(current as *mut u8, Layout::new::<Node>());
            current = next;
            //@ close Nodes(current);
        }
        //@ open Nodes(current);
        //@ open_struct(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let stack = Stack::create();
        //@ close Nodes(std::ptr::null_mut());
        Stack::push(stack, 10);
        Stack::push(stack, 20);
        let _ = Stack::pop(stack);
        Stack::dispose(stack);
    }
}