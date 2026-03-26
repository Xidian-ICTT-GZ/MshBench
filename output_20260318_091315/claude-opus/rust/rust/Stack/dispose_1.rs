use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

predicate nodes(struct Node *n;) =
    n == std::ptr::null_mut() ?
        emp
    :
        
        n |-> Node(_, ?next)
        &*& nodes(next);

predicate stack(struct Stack *s;) =
    s |-> Stack(?head)
    &*& nodes(head);

unsafe fn dispose_nodes(n: *mut Node)
    #[requires(nodes(n))]
    #[ensures(emp)]
{
    if !n.is_null() {
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
        #[requires(stack != std::ptr::null_mut() &*& stack(stack))]
        #[ensures(emp)]
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}