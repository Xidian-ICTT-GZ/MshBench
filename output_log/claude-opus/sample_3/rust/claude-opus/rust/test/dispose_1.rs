use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(n: *mut Node; count: int) =
    if n == null {
        count == 0
    } else {
        count > 0 &*&
        n->value |-> _ &*&
        n->next |-> ?next &*&
        malloc_block_Node(n) &*&
        nodes(next, count - 1)
    };

predicate stack(s: *mut Stack; count: int) =
    s->head |-> ?h &*&
    malloc_block_Stack(s) &*&
    nodes(h, count);

#[requires(nodes(n, count))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node)
    //@ decreases count
{
    if n != null {
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(stack(stack, count))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
        //@ decreases count
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}