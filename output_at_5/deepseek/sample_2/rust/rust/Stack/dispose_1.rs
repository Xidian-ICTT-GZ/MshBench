use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

unsafe fn dispose_nodes(n: *mut Node)
    //@ req node(n);
    //@ ens true;
{
    if !n.is_null() {
        //@ open node(n);
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    } else {
        //@ open node(n);
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
        //@ req stack(stack);
        //@ ens true;
    {
        //@ open stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}

/*@
pred node(n: *mut Node) = 
    n != 0 ? 
        struct_Node_padding(n) &*&
        (*n).value |-> _ &*&
        (*n).next |-> ?next &*&
        node(next)
    :
        true;

pred stack(s: *mut Stack) = 
    s != 0 &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> ?head &*&
    node(head);
@*/