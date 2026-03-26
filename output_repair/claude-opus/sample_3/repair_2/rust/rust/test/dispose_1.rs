use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Nodes(n: *mut Node;) =
    if n == 0 {
        true
    } else {
        (*n).value |-> ?_ &*& (*n).next |-> ?next &*& struct_Node_padding(n) &*& Nodes(next)
    };

pred Stack_(s: *mut Stack;) =
    (*s).head |-> ?head &*& struct_Stack_padding(s) &*& Nodes(head);

@*/

unsafe fn dispose_nodes(n: *mut Node)
//@ req Nodes(n);
//@ ens true;
{
    //@ open Nodes(n);
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack_(stack);
    //@ ens true;
    {
        //@ open Stack_(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}