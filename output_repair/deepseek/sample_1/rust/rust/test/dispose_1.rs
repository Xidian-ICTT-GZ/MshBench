use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_list(n: *mut Node) -> bool {
    n.is_null() || (
        exists(|next: *mut Node| {
            n as usize > 0 &&
            node_list(next)
        })
    )
}

#[predicate]
fn stack_valid(s: *mut Stack) -> bool {
    s as usize > 0 &&
    exists(|head: *mut Node| {
        node_list(head)
    })
}

#[requires(node_list(n))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(stack_valid(stack))]
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