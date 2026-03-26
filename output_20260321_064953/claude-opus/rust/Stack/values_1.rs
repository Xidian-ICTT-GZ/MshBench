use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred node(n: *mut Node) = n != std::ptr::null_mut() &*& malloc_block_Node(n) &*&
//@     (exists<nxt> * mut Node, val> &*& n->next |-> nxt &*& n->value |-> val &*& node(nxt)) || (n->next == std::ptr::null_mut());

//@ pred stack(s: *mut Stack, top: *mut Node) = s != std::ptr::null_mut() &*& malloc_block_Stack(s) &*& s->head |-> top &*& (top == std::ptr::null_mut() || node(top));

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result, std::ptr::null_mut());
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close stack(stack, std::ptr::null_mut());
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack != std::ptr::null_mut() &*& stack(stack, ?top);
    //@ ensures stack(stack, ?new_top) &*& new_top == _;
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close node(n);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ open stack(stack, top);
        //@ close stack(stack, n);
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack != std::ptr::null_mut() &*& stack(stack, std::ptr::null_mut());
    //@ ensures true;
    {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}