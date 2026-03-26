use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate Nodes(*mut Node n; list<i32> vs) =
    match vs {
        [] => n == null(),
        v :: vs1 => n != null() && *n |-> struct Node { value: v, next: ?n1 } &*& Nodes(n1, vs1)
    };

unsafe fn dispose_nodes(n: *mut Node)
    requires Nodes(n, ?vs);
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
        requires *stack |-> struct Stack { head: ?head } &*& Nodes(head, ?vs);
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