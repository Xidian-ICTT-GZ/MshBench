use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {

    /*@
    pred nodes(*mut Node n;) =
        n == std::ptr::null_mut() ?
            true
        :
            n->next |-> ?next &*& n->value |-> _ &*& nodes(next);
    @*/

    /*@
    pred stack(*mut Stack s;) =
        s->head |-> ?h &*& nodes(h);
    @*/

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(std::ptr::null_mut());
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
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(n);
        //@ close stack(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack);
    //@ ensures true;
    {
        //@ open stack(stack);
        let mut current = (*stack).head;
        while current != std::ptr::null_mut()
        //@ invariant nodes(current);
        {
            //@ open nodes(current);
            let next = (*current).next;
            dealloc(current as *mut u8, Layout::new::<Node>());
            current = next;
        }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}