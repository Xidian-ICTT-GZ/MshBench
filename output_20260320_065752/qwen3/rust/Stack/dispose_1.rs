use std::alloc::{dealloc, Layout};

/*@ pred node(p: *mut Node, v: i32, next: *mut Node) = 
    p != 0 &*& alloc_block(p as *u8, std::mem::size_of::<Node>()) &*& 
    struct_Node_padding(p) &*& 
    (*p).value |-> v &*& (*p).next |-> next;
@*/

/*@ pred stack(p: *mut Stack, head: *mut Node) = 
    p != 0 &*& alloc_block(p as *u8, std::mem::size_of::<Stack>()) &*& 
    struct_Stack_padding(p) &*& 
    (*p).head |-> head;
@*/

unsafe fn dispose_nodes(n: *mut Node)
//@ req n == 0 ? true : node(n, ?v, ?next) &*& n != 0;
//@ ens true;
{
    
    if !n.is_null() {
        //@ open node(n, ?v, ?next);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack == 0 ? true : stack(stack, ?head) &*& stack != 0;
    //@ ens true;
    {
        
        //@ open stack(stack, ?head);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}