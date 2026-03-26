use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(n: *mut Node) =
    n.is_null() ? true : (
        n as usize != 0 &&
        Owned(n) &&
        Owned((*n).value) &&
        Owned((*n).next) &&
        node_list((*n).next)
    );

#[requires(node_list(n))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(Owned(stack) && Owned((*stack).head) && node_list((*stack).head))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}