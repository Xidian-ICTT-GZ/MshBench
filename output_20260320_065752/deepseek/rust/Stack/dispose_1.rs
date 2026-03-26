use std::alloc::{dealloc, Layout};

/*@
pred Node(n: *mut Node; v: i32, next: *mut Node) =
    alloc_block(n, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).value |-> v &*&
    (*n).next |-> next;
@*/

struct Node {
    value: i32,
    next: *mut Node,
}

/*@
pred Stack(s: *mut Stack; head: *mut Node) =
    alloc_block(s, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> head;
@*/

struct Stack {
    head: *mut Node,
}

unsafe fn dispose_nodes(n: *mut Node)
    //@ req Node(n, _, _);
    //@ ens true;
{
    if !n.is_null() {
        //@ open Node(n, _, _);
        let next = (*n).next;
        //@ close Node(n, _, next);
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    } else {
        //@ close Node(n, _, _);
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
        //@ req Stack(stack, _);
        //@ ens true;
    {
        //@ open Stack(stack, _);
        let head = (*stack).head;
        //@ close Stack(stack, head);
        dispose_nodes(head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}