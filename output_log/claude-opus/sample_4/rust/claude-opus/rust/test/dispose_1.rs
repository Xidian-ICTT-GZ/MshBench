use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(n: *mut Node; count: int) =
    if n == 0 as *mut Node {
        count == 0
    } else {
        count > 0 &*&
        (*n).value |-> _ &*&
        (*n).next |-> ?next &*&
        malloc_block_Node(n) &*&
        nodes(next, count - 1)
    };

predicate stack(s: *mut Stack; count: int) =
    (*s).head |-> ?h &*&
    malloc_block_Stack(s) &*&
    nodes(h, count);

#[requires(nodes(n, ?c) &*& c > 0)]
#[ensures(nodes(n, 0))]
unsafe fn dispose_nodes(n: *mut Node)
    decreases c
{
    if n != 0 as *mut Node {
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(stack(stack, ?c) &*& c >= 0)]
    #[ensures(stack(stack, 0) == false)]
    unsafe fn dispose(stack: *mut Stack)
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}