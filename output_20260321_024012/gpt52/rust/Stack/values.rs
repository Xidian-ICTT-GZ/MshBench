use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred node(p: *mut Node) = p != std::ptr::null_mut() && (*p).next |-> ?n &*& (*p).value |-> ?v;
//@ pred stack(p: *mut Stack) = p != std::ptr::null_mut() && (*p).head |-> ?h;

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result);
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close stack(stack);
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack);
    //@ ens stack(stack);
    
    
    {
        //@ open stack(stack);
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close node(n);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        
        //@ close stack(stack);
        
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    
    
    {
        //@ open stack(stack);
        
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}