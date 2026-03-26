use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

pred node_chain(n: *mut Node) =
    if n == std::ptr::null_mut() {
        true
    } else {
        (*n).value |-> ?v &*& (*n).next |-> ?next &*& node_chain(next)
    };

pred stack_with_nodes(stack: *mut Stack) =
    (*stack).head |-> ?h &*& node_chain(h);

@*/

unsafe fn dispose_nodes(n: *mut Node)
    //@ req node_chain(n);
    //@ ens true;
    
    
{
    //@ open node_chain(n);
    
    if !n.is_null() {
        dispose_nodes((*n).next);
        //@ open node_chain((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
        //@ req stack_with_nodes(stack);
        //@ ens true;
        
        
    {
        //@ open stack_with_nodes(stack);
        
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}