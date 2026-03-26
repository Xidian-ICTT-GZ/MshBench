use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

//@ pred node<n>(p: *mut Node) = p != 0 && malloc_block_Node(p) &*& p->value |-> _ &*& p->next |-> ?next &*& node<n-1>(next) && n > 0 || p == 0 && n == 0;

unsafe fn dispose_nodes(n: *mut Node)
    //@ req node(?n_len)(n);
    //@ ensures node<0>(n);
{
    if !n.is_null() {
        //@ open node(?n_len)(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
        //@ close node<0>(0);
    } else {
        //@ close node<0>(0);
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
        //@ req stack != 0 &*& malloc_block_Stack(stack) &*& node(?n_len)((*stack).head);
        //@ ensures true;
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}