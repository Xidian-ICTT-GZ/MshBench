use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Node(n: *mut Node; v: i32, next: *mut Node) =
    alloc_block(n, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).value |-> v &*&
    (*n).next |-> next;
@*/

/*@
pred lseg(start: *mut Node, end: *mut Node) =
    start == end ?
        true
    :
        Node(start, _, next) &*& lseg(next, end);
@*/

/*@
pred Stack(s: *mut Stack) =
    alloc_block(s, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> head &*&
    lseg(head, std::ptr::null_mut());
@*/

unsafe fn dispose_nodes(n: *mut Node)
    //@ req lseg(n, std::ptr::null_mut());
    //@ ens true;
{
    if !n.is_null() {
        //@ open lseg(n, std::ptr::null_mut());
        //@ open Node(n, _, _);
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    } else {
        //@ open lseg(std::ptr::null_mut(), std::ptr::null_mut());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
        //@ req Stack(stack);
        //@ ens true;
    {
        //@ open Stack(stack);
        //@ open lseg((*stack).head, std::ptr::null_mut());
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}