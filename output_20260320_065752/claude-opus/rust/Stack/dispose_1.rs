use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

/*@ 
predicate node(struct Node* n; int value, struct Node* next) = 
    n->value |-> value &*& n->next |-> next;
@*/

/*@ 
predicate nodes(struct Node* n) = 
    n == 0 ? true : 
    node(n, ?v, ?next) &*& nodes(next);
@*/

struct Stack {
    head: *mut Node,
}

/*@ 
predicate stack(struct Stack* s) = 
    s->head |-> ?h &*& nodes(h);
@*/

//@ req n != 0 &*& nodes(n);
//@ ensures true;
unsafe fn dispose_nodes(n: *mut Node)
{
    if !n.is_null() {
        //@ open nodes(n);
        //@ open node(n, _, _);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
        //@ close nodes(n);
    }
}

//@ req stack != 0 &*& stack(stack);
//@ ensures true;
impl Stack {
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("Dispose functions compile successfully!");
}