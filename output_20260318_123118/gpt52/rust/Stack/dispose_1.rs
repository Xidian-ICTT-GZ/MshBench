use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate node(p: *mut Node; next: *mut Node) =
    std::ptr::raw_field(p, "value") |-> ?v &*&
    std::ptr::raw_field(p, "next") |-> next;

predicate nodes(n: *mut Node) =
    n == std::ptr::null_mut() ?
        emp
    :
        node(n, ?nx) &*& nodes(nx);

predicate stack(s: *mut Stack) =
    std::ptr::raw_field(s, "head") |-> ?h &*& nodes(h);

@*/

#[requires(nodes(n))]
#[ensures(emp)]
unsafe fn dispose_nodes(n: *mut Node)
{
    if !n.is_null() {
        /*@
        open nodes(n);
        open node(n, ?nx);
        @*/
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    } else {
        /*@ open nodes(n); @*/
    }
}

impl Stack {
    #[requires(stack(stack))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack)
    {
        /*@ open stack(stack); @*/
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}