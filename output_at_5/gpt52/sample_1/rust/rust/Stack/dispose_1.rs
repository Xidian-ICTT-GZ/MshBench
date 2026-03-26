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
        (*n).value |-> ?v &*& (*n).next |-> ?nx &*& nodes(nx);

pred stack(stack: *mut Stack) =
    (*stack).head |-> ?h &*& nodes(h);

@*/

unsafe fn dispose_nodes(n: *mut Node)
    //@ req nodes(n);
    //@ ens true;
{
    //@ open nodes(n);
    if !n.is_null() {
        dispose_nodes((*n).next);
        //@ open nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
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