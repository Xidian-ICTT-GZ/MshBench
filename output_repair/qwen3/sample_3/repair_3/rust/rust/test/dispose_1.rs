use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(*mut Node n;) = 
    n == null() ? emp : (
        n as usize > 0 &*&
        struct_Node_padding(n) &*&
        (*n).value |-> _ &*&
        (*n).next |-> ?next &*&
        node_list(next)
    );

predicate stack_valid(*mut Stack s;) = 
    s as usize > 0 &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> ?head &*&
    node_list(head);

unsafe fn dispose_nodes(n: *mut Node)
    requires node_list(n),
    ensures emp;
{
    if !n.is_null() {
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
        requires stack_valid(stack),
        ensures emp;
    {
        let head = (*stack).head;
        dispose_nodes(head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}