use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

//@ predicate nodes(struct Node *n) = n == 0 ? true : (pointer(n, _) &*& nodes((*n).next));

unsafe fn dispose_nodes(n: *mut Node)
    //@ requires nodes(n);
    //@ ensures true;
{
    if !n.is_null() {
        //@ open nodes(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
        //@ close nodes(n);
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
        //@ requires pointer(stack, _) &*& nodes((*stack).head);
        //@ ensures true;
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}