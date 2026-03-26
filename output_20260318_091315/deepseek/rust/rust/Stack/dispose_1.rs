use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_own(n: *mut Node) -> bool {
    alloc::allocated(n) && struct_ty!(@n) == Node
}

#[predicate]
fn nodes_own(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        node_own(n) && nodes_own((*n).next)
    }
}

#[predicate]
fn stack_own(s: *mut Stack) -> bool {
    alloc::allocated(s) && struct_ty!(@s) == Stack
}

#[predicate]
fn full_stack_own(s: *mut Stack) -> bool {
    stack_own(s) && nodes_own((*s).head)
}

unsafe fn dispose_nodes(n: *mut Node)
    #[requires(nodes_own(n))]
    #[ensures(true)]
{
    if !n.is_null() {
        let next = (*n).next;
        #[invariant(nodes_own(n))]
        {
            dispose_nodes(next);
        }
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
        #[requires(full_stack_own(stack))]
        #[ensures(true)]
    {
        let head = (*stack).head;
        #[invariant(full_stack_own(stack))]
        {
            dispose_nodes(head);
        }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}