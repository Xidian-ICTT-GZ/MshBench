use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

//@ pred node(n: *mut Node) = 
//@     n != std::ptr::null_mut() &*&
 //@    pointer(n) &*&
 //@    field(n, "next", ?next) &*&
 //@    field(n, "value", _) &*&
 //@    true;

struct Stack {
    head: *mut Node,
}

//@ pred stack(s: *mut Stack, ?nodes: list<*mut Node>) = 
//@     s != std::ptr::null_mut() &*&
 //@    pointer(s) &*&
 //@    field(s, "head", ?h) &*&
 //@    (h == std::ptr::null_mut() ? true : node(h)) &*&
 //@    true;

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result, []);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack != std::ptr::null_mut() &*& stack(stack, ?nodes);
    //@ ensures stack(stack, cons(_, nodes));
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
    //@ requires stack != std::ptr::null_mut() &*& stack(stack, cons(?n, ?nodes));
    //@ ensures stack(stack, nodes);
    {
        
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack != std::ptr::null_mut() &*& stack(stack, []);
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
        let result1 = Stack::pop(s);
        
        let result2 = Stack::pop(s);
        
        Stack::dispose(s);
    }
}