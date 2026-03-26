//@ pred Nodes(*mut Node;);

use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

//@ pred Nodes(n: *mut Node) = n == std::ptr::null_mut::<Node>() || 
//@   (n as *mut u8).is_aligned(Layout::new::<Node>().align()) &*&
//@   [_]std::alloc::alloc_block(n as *mut u8, Layout::new::<Node>()) &*&
//@   struct_Node_padding(n) &*&
//@   (*n).value |-> ?v &*& (*n).next |-> ?next &*& Nodes(next);

unsafe fn dispose_nodes(n: *mut Node)
//@ req Nodes(n);
//@ ens true;
{
    
    if !n.is_null() {
        //@ open Nodes(n);
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack as *mut u8 != null &*& 
    //@      [_]std::alloc::alloc_block(stack as *mut u8, Layout::new::<Stack>()) &*&
    //@      struct_Stack_padding(stack) &*&
    //@      (*stack).head |-> ?h &*& Nodes(h);
    //@ ens true;
    {
        
        let h = (*stack).head;
        dispose_nodes(h);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}