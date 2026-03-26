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
        //@ open Node { value: _, next: next };
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

//@ pred node(n: *mut Node; v: i32, next: *mut Node) {
//@     n != 0 &*& struct_Node_padding(n) &*& (*n).value |-> v &*& (*n).next |-> next;
//@ }

//@ pred stack(s: *mut Stack; head: *mut Node) {
//@     s != 0 &*& struct_Stack_padding(s) &*& (*s).head |-> head;
//@ }