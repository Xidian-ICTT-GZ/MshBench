use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate node(struct Node *n; struct Node *next, i32 v) =
    n->next |-> next &*& n->value |-> v;

predicate nodes(struct Node *n) =
    n == 0 ?
        emp
    :
        node(n; ?next, ?v) &*& nodes(next);

predicate stack(struct Stack *s) =
    s->head |-> ?h &*& nodes(h);

@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ requires emp;
    //@ ensures stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        //@ close nodes(0);
        //@ close stack(stack);

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack);
    //@ ensures stack(stack);
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open nodes(?oldh);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;

        //@ close node(n; oldh, value);
        //@ close nodes(n);
        //@ close stack(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack);
    //@ ensures emp;
    {
        //@ open stack(stack);
        //@ open nodes(?h);
        //@ close nodes(h);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}