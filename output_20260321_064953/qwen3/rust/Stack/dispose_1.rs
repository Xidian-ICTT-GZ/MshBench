//@ predicate Nodes(*mut Node;);

//@ predicate Stack_own(*mut Stack, *mut Node) = 
//@   std::ptr::addr_of!((*Stack).head) |-> ?head &*& 
//@   Nodes(head);

//@ predicate Nodes(n: *mut Node) = 
//@   n == std::ptr::null_mut::<Node>() ? 
//@     true 
//@   : 
//@     std::ptr::addr_of!((*n).value) |-> _ &*& 
//@     std::ptr::addr_of!((*n).next) |-> ?next &*& 
//@     Nodes(next) &*& 
//@     std::alloc::alloc_block(n as *mut u8, std::alloc::Layout::new::<Node>());

use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req Nodes(n);
//@ ens true;
{
    
    if !n.is_null() {
        //@ open Nodes(n);
        let next = (*n).next;
        dealloc(n as *mut u8, Layout::new::<Node>());
        dispose_nodes(next);
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack_own(stack, ?head) &*& std::alloc::alloc_block(stack as *mut u8, std::alloc::Layout::new::<Stack>());
    //@ ens true;
    {
        
        //@ open Stack_own(stack, _);
        let head = (*stack).head;
        dealloc(stack as *mut u8, Layout::new::<Stack>());
        dispose_nodes(head);
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}