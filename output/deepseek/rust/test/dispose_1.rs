use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_own(n: *mut Node, value: i32, next: *mut Node) -> bool {
    struct_own!{n => Node { value, next }}
}

#[predicate]
fn nodes(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        exists!(value: i32, next: *mut Node =>
            node_own(n, value, next) * nodes(next))
    }
}

#[predicate]
fn stack_own(s: *mut Stack, head: *mut Node) -> bool {
    struct_own!{s => Stack { head }} * nodes(head)
}

#[requires(stack_own(stack, head))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        #[invariant(nodes(n))]
        let next = (*n).next;
        dispose_nodes(next);
        #[assert(node_own(n, _, _))]
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(stack_own(stack, head))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        #[assert(stack_own(stack, head))]
        let head = (*stack).head;
        dispose_nodes(head);
        #[assert(stack_own(stack, _))]
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}