use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result != 0 &*& node_own(result, _);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close node_own(stack, _);
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req node_own(stack, ?head) &*& malloc_block_node(head);
    //@ ens node_own(stack, ?newHead) &*& malloc_block_node(newHead);
    {
        //@ open node_own(stack, head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node_own(stack, n);
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req node_own(stack, ?head) &*& head != 0 &*& malloc_block_node(head);
    //@ ens node_own(stack, ?next) &*& malloc_block_node(next);
    {
        //@ open node_own(stack, head);
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close node_own(stack, (*stack).head);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req node_own(stack, 0);
    //@ ens true;
    {
        //@ open node_own(stack, _);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

//@ predicate node_own(*mut Stack stack, *mut Node head) = malloc_block_Stack(stack) &*& struct_Stack_padding(stack) &*& (*stack).head |-> head;

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);
        let result2 = Stack::pop(s);
        Stack::dispose(s);
    }
}