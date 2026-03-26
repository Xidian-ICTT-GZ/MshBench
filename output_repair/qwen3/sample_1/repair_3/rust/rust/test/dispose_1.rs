use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node(*mut Node n, i32 v, *mut Node next) =
    n != null &*&
    [1/2]n as *mut i32 |-> v &*&
    [1/2](&(*n).next) |-> next;

predicate nodes(*mut Node n) =
    n == null ?
        true
    :
        node(n, ?v, ?next) &*& nodes(next);

#[requires(nodes(n))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(*stack as *Stack |-> ?s &*& s.head |-> ?head &*& nodes(head))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        let head = (*stack).head;
        dispose_nodes(head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}