use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred node(p: *mut Node, next: *mut Node, v: i32) =
    std::alloc::alloc_block(p as *mut u8, Layout::new_::<Node>()) &*&
    (*p).next |-> next &*&
    (*p).value |-> v;

pred nodes(p: *mut Node) =
    p == std::ptr::null_mut() ?
        true
    :
        node(p, ?n, ?v) &*& nodes(n);

pred stack(s: *mut Stack) =
    std::alloc::alloc_block(s as *mut u8, Layout::new_::<Stack>()) &*&
    (*s).head |-> ?h &*& nodes(h);

@*/

impl Stack {

    //@ req true;
    //@ ens stack(result);
    unsafe fn create() -> *mut Stack
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close nodes(std::ptr::null_mut());
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack);
        
        
        stack
    }
    
    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32)
    
    
    {
        //@ open stack(stack);
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n, (*stack).head, value);
        //@ close nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
        
        
    }
    
    //@ req stack(stack) &*& (*stack).head |-> ?h &*& h != std::ptr::null_mut();
    //@ ens stack(stack);
    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        //@ open stack(stack);
        
        let head = (*stack).head;
        //@ open nodes(head);
        //@ open node(head, ?next, ?v);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        
        result
    }
    
    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn reverse(stack: *mut Stack)
    
    
    {
        //@ open stack(stack);
        
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close nodes(m);
        
        
        loop {
            //@ inv nodes(n) &*& nodes(m);
            
            if n.is_null() {
                break;
            }
            
            //@ open nodes(n);
            //@ open node(n, ?next, ?v);
            let next = (*n).next;
            
            (*n).next = m;
            //@ close node(n, m, v);
            m = n;
            //@ close nodes(m);
            n = next;
            
            
        }
        
        (*stack).head = m;
        //@ close stack(stack);
        
    }

    //@ req stack(stack) &*& (*stack).head |-> std::ptr::null_mut();
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        //@ open stack(stack);
        //@ open nodes(std::ptr::null_mut());
        
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
        let _ = (result1, result2);
    }
}