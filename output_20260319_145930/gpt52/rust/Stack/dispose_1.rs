use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(n: *mut Node) =
    n == std::ptr::null_mut() ?
        true
    :
        alloc_block_Node(n) &*&
        (*n).value |-> ?v &*&
        (*n).next |-> ?nx &*&
        nodes(nx);

pred stack(s: *mut Stack) =
    alloc_block_Stack(s) &*&
    (*s).head |-> ?h &*&
    nodes(h);

@*/

//@ req nodes(n);
//@ ens true;
unsafe fn dispose_nodes(n: *mut Node)
    
    
{
    
    if !n.is_null() {
        //@ open nodes(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
        
        
    {
        
        //@ open stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}