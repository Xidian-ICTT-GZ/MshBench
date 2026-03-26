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
    alloc::allocated(n as *mut u8, Layout::new::<Node>()) &&
    struct_Node! { n => { value: v, next: next } } &&
    v.is_int() &&
    (if next.is_null() { true } else { node_own(next) })
}

#[predicate]
fn stack_own(s: *mut Stack) -> bool {
    alloc::allocated(s as *mut u8, Layout::new::<Stack>()) &&
    struct_Stack! { s => { head: head } } &&
    (if head.is_null() { true } else { node_own(head) })
}

#[requires(stack_own(stack))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node)
{
    if !n.is_null() {
        #[invariant(node_own(n))]
        {
            let next = (*n).next;
            dispose_nodes(next);
            dealloc(n as *mut u8, Layout::new::<Node>());
        }
    }
}

impl Stack {
    #[requires(stack_own(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
    {
        #[invariant(stack_own(stack))]
        {
            dispose_nodes((*stack).head);
            dealloc(stack as *mut u8, Layout::new::<Stack>());
        }
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}