use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred nodes_(n: *mut Node) =
    n == 0 ?
        true
    :
        std::alloc::alloc_block(n as *mut u8, Layout::new::<Node>()) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        nodes_(next);

pred stack_(s: *mut Stack) =
    std::alloc::alloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    (*s).head |-> ?h &*&
    nodes_(h);
@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack_(result);
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes_(0);
        //@ close stack_(stack);
        
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack_(stack);
    //@ ens stack_(stack);
    
    
    {
        //@ open stack_(stack);
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes_(n);
        //@ close stack_(stack);
        
        
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack_(stack) &*& (*stack).head |-> ?h &*& h != 0;
    //@ ens stack_(stack);
    
    
    {
        //@ open stack_(stack);
        
        let head = (*stack).head;
        
        //@ open nodes_(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack_(stack);
        
        result
    }
    
    unsafe fn reverse(stack: *mut Stack)
    //@ req stack_(stack);
    //@ ens stack_(stack);
    
    
    {
        //@ open stack_(stack);
        
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close nodes_(0);
        
        loop {
            //@ inv nodes_(m) &*& nodes_(n);
            
            if n.is_null() {
                break;
            }
            
            //@ open nodes_(n);
            let next = (*n).next;
            
            (*n).next = m;
            //@ close nodes_(n);
            m = n;
            n = next;
            
            
        }
        
        (*stack).head = m;
        //@ close stack_(stack);
        
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack_(stack) &*& (*stack).head |-> ?h &*& h == 0;
    //@ ens true;
    
    
    {
        //@ open stack_(stack);
        //@ open nodes_(h);
        
        
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