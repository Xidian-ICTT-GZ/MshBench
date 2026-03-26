use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(*mut Node n;);

predicate stack_valid(*mut Stack s;) = 
    s as usize > 0 &*&
    exists(?head) &*&
    struct_Stack_padding(s) &*&
    struct_Stack_head(s, head) &*&
    node_list(head);

predicate node_list(*mut Node n;) =
    n == null() ? true :
    (
        n as usize > 0 &*&
        struct_Node_padding(n) &*&
        struct_Node_value(n, ?v) &*&
        struct_Node_next(n, ?next) &*&
        node_list(next)
    );

unsafe fn dispose_nodes(n: *mut Node)
    requires node_list(n),
    ensures true;
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
        ensures true;
    {
        let head = (*stack).head;
        dispose_nodes(head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}