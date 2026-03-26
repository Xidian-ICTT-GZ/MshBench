use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(*mut Node n; *mut Node rest) =
    n == null() ?
        rest == null()
    :
        n as usize > 0 &*&
        struct_Node_padding(n) &*&
        struct_Node_value(n, ?v) &*&
        struct_Node_next(n, ?next_ptr) &*&
        node_list(next_ptr, rest);

predicate stack_valid(*mut Stack s; *mut Node head) =
    s as usize > 0 &*&
    struct_Stack_padding(s) &*&
    struct_Stack_head(s, head) &*&
    node_list(head, null());

unsafe fn dispose_nodes(n: *mut Node)
    requires node_list(n, null());
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
        requires stack_valid(stack, null());
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