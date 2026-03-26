use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

//@ predicate nodes(*mut Node n) = n != std::ptr::null_mut() ? (malloc_block_Node(n) &*& *n.value |-> _ &*& *n.next |-> ?next &*& nodes(next)) : true;

unsafe fn dispose_nodes(n: *mut Node)
    //@ req nodes(n);
    //@ ensures true;
{
    if !n.is_null() {
        //@ open nodes(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
        //@ req malloc_block_Stack(stack) &*& nodes((*stack).head);
        //@ ensures true;
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}