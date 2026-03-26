use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate Nodes(*mut Node n;);

predicate Stack_own(*mut Stack s;);

predicate Nodes(null;) = true;
predicate Nodes(n) = n != null &*&
    struct_Node_padding(n) &*&
    struct_Node_value(n, ?v) &*&
    struct_Node_next(n, ?next) &*&
    Nodes(next) &*&
    [_]malloc_block_Node(n);

unsafe fn dispose_nodes(n: *mut Node)
    #[requires(Nodes(n))]
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
        #[requires(Stack_own(stack))]
        #[ensures(true)]
    {
        open Stack_own(stack);
        let head = (*stack).head;
        dispose_nodes(head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

predicate Stack_own(s) =
    s != null &*&
    struct_Stack_padding(s) &*&
    struct_Stack_head(s, ?head) &*&
    Nodes(head) &*&
    [_]malloc_block_Stack(s);

fn main() {
    println!("Dispose functions compile successfully!");
}