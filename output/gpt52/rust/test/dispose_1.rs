use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate node_block(struct Node *n; struct Node *next, i32 value) =
    n->value |-> value &*& n->next |-> next &*& alloc_block(n, Layout::new::<Node>());

predicate nodes(struct Node *n) =
    n == 0 ?
        emp
    :
        node_block(n, ?next, ?value) &*& nodes(next);

predicate stack_block(struct Stack *s; struct Node *head) =
    s->head |-> head &*& alloc_block(s, Layout::new::<Stack>());

predicate stack(struct Stack *s) =
    stack_block(s, ?head) &*& nodes(head);

@*/

unsafe fn dispose_nodes(n: *mut Node)
/*@ requires nodes(n); @*/
/*@ ensures emp; @*/
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
    /*@ requires stack(stack); @*/
    /*@ ensures emp; @*/
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}