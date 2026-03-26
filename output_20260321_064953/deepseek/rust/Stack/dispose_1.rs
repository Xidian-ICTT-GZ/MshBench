use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

unsafe fn dispose_nodes(n: *mut Node)
    //@ req node(n, _);
    //@ ens true;
{
    //@ open node(n, _);
    if !n.is_null() {
        //@ let next = (*n).next;
        //@ open node(n, _);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
        //@ req stack(stack, _);
        //@ ens true;
    {
        //@ open stack(stack, _);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}

/*@
pred node(n: *mut Node; v: i32) {
    if (n.is_null()) {
        true
    } else {
        alloc_block(n, std::mem::size_of::<Node>()) &*& struct_Node_padding(n) &*&
        (*n).value |-> v &*&
        (*n).next |-> ?next &*& node(next, _)
    }
}

pred stack(s: *mut Stack; head: *mut Node) {
    alloc_block(s, std::mem::size_of::<Stack>()) &*& struct_Stack_padding(s) &*&
    (*s).head |-> head &*& node(head, _)
}
@*/