use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

// Ghost predicate definitions for stack state
//@ ghost predicate stack_head(stack: *mut Stack, head: *mut Node) = 
//@     stack != 0 && read_ptr::<Stack>(stack).head == head;

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result != 0 && stack_head(result, null_pointer);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack != 0 && stack_head(stack, _);
    //@ ens stack_head(stack, _);
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
    //@ req stack != 0 && stack_head(stack, head) && head != 0;
    //@ ens stack_head(stack, _);
    {
        
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack != 0 && stack_head(stack, null_pointer);
    //@ ens true;
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