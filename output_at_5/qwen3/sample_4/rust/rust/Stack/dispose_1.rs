use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

//@ ghost pred node_valid(n: *mut Node) = n == null || (n != null && true && true && node_valid((*n).next));
//@ ghost pred stack_valid(s: *mut Stack) = s != null && node_valid((*s).head);

unsafe fn dispose_nodes(n: *mut Node)
//@ requires n == null || node_valid(n);
//@ ensures true;
{
    
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
//@ requires stack != null && stack_valid(stack);
//@ ensures true;
    {
        
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}