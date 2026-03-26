use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@ predicate nodes(?n: list<int>, *node: *mut Node) =
    switch n {
        case nil => node == std::ptr::null_mut()
        case cons(h, t) => node != std::ptr::null_mut() &*&
            node->next |-> ?next &*& node->value |-> h &*&
            nodes(t, next)
    };
@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures true;
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack != std::ptr::null_mut() &*& chars::malloc_block(stack, _);
    //@ ensures chars::malloc_block(stack, _);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack != std::ptr::null_mut() &*& (*stack).head != std::ptr::null_mut() &*&
    //@          nodes(?vals, (*stack).head);
    //@ ensures nodes(tail(vals), (*stack).head) &*& result == head(vals);
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack != std::ptr::null_mut();
    //@ ensures true;
    {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}