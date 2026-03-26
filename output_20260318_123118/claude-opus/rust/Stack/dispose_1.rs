use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(struct Node *n;) =
    n == 0 ?
        emp
    :
        n->value |-> _ &*& n->next |-> (struct Node *next) &*& nodes(next);

predicate stack(struct Stack *s;) =
    s->head |-> (struct Node *head) &*& nodes(head);

unsafe fn dispose_nodes(n: *mut Node)
    #[requires(nodes(n))]
    #[ensures(true)]
{
    if !n.is_null() {
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
        #[requires(stack(stack))]
        #[ensures(true)]
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}