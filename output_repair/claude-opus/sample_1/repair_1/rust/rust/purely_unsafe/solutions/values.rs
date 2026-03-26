use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Node_next(n: *mut Node; next: *mut Node) =
    (*n).next |-> next;

pred Node_value(n: *mut Node; value: i32) =
    (*n).value |-> value;

pred Node_own(n: *mut Node; next: *mut Node, value: i32) =
    Node_next(n, next) &*& Node_value(n, value) &*& alloc_block(n as *mut u8, Layout::new_::<Node>());

pred Stack_head(s: *mut Stack; head: *mut Node) =
    (*s).head |-> head;

pred Stack_own(s: *mut Stack; head: *mut Node) =
    Stack_head(s, head) &*& alloc_block(s as *mut u8, Layout::new_::<Stack>());

pred Nodes(n: *mut Node;) =
    if n == std::ptr::null_mut() {
        true
    } else {
        Node_own(n, ?next, ?value) &*& Nodes(next)
    };

pred Stack_valid(s: *mut Stack;) =
    Stack_own(s, ?head) &*& Nodes(head);

@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack_valid(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close Stack_head(stack, std::ptr::null_mut());
        (*stack).head = std::ptr::null_mut();
        //@ close Stack_own(stack, std::ptr::null_mut());
        //@ close Nodes(std::ptr::null_mut());
        //@ close Stack_valid(stack);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack_valid(stack);
    //@ ens Stack_valid(stack);
    {
        //@ open Stack_valid(stack);
        //@ open Stack_own(stack, ?old_head);
        //@ open Stack_head(stack, old_head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close Node_next(n, old_head);
        (*n).next = (*stack).head;
        //@ close Node_value(n, value);
        (*n).value = value;
        //@ close Node_own(n, old_head, value);
        //@ close Nodes(n);
        //@ close Stack_head(stack, n);
        (*stack).head = n;
        //@ close Stack_own(stack, n);
        //@ close Stack_valid(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack_own(stack, std::ptr::null_mut());
    //@ ens true;
    {
        //@ open Stack_own(stack, std::ptr::null_mut());
        //@ open Stack_head(stack, std::ptr::null_mut());
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}