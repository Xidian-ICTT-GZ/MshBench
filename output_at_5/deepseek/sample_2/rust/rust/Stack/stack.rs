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
    //@ ens ptr::<Stack>(result, _);
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close ptr::<Stack>(stack, _);
        
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req ptr::<Stack>(stack, ?stack_own) &*& stack_own.head |-> ?head;
    //@ ens ptr::<Stack>(stack, {head: ?new_head}) &*& ptr::<Node>(new_head, {next: head, value: value});
    
    
    {
        //@ open ptr::<Stack>(stack, _);
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close ptr::<Node>(n, _);
        //@ close ptr::<Stack>(stack, _);
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req ptr::<Stack>(stack, {head: ?head}) &*& head != 0 &*& ptr::<Node>(head, {next: ?next, value: ?v});
    //@ ens ptr::<Stack>(stack, {head: next}) &*& v == result;
    
    
    {
        //@ open ptr::<Stack>(stack, _);
        
        let head = (*stack).head;
        //@ open ptr::<Node>(head, _);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close ptr::<Stack>(stack, _);
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req ptr::<Stack>(stack, {head: 0});
    //@ ens true;
    
    
    {
        //@ open ptr::<Stack>(stack, _);
        
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()
//@ req true;
//@ ens true;

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