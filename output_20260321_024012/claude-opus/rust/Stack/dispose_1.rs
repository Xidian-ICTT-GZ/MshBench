use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

//@ pred nodes(n: *mut Node) = 
//@     n == std::ptr::null_mut() ? emp :
//@     n |-> Node { value: _, next: ?next } &*& nodes(next);

unsafe fn dispose_nodes(n: *mut Node)
    //@ req nodes(n);
    //@ ens true;
{
    if !n.is_null() {
        //@ open nodes(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
        //@ close nodes(std::ptr::null_mut());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
        //@ req stack != std::ptr::null_mut() &*& nodes((*stack).head);
        //@ ens true;
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}