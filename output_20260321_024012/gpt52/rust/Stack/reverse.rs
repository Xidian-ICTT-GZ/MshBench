use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(ptr: *mut Node) =
    ptr == 0 ?
        true
    :
        (*ptr).next |-> ?next &*&
        (*ptr).value |-> ?v &*&
        nodes(next);

pred stack(stack: *mut Stack) =
    (*stack).head |-> ?head &*&
    nodes(head);

@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result != 0 &*& stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(0);
        //@ close stack(stack);
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack != 0 &*& stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
        
        
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack != 0 &*& stack(stack) &*& (*stack).head |-> ?head &*& head != 0;
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        //@ close stack(stack);
        result
    }
    
    unsafe fn reverse(stack: *mut Stack)
    //@ req stack != 0 &*& stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close nodes(m);
        //@ close nodes(n);
        
        
        loop {
            //@ inv nodes(n) &*& nodes(m);
            
            if n.is_null() {
                break;
            }
            
            //@ open nodes(n);
            let next = (*n).next;
            
            (*n).next = m;
            m = n;
            n = next;
            //@ close nodes(m);
            
            
        }
        
        //@ open nodes(n);
        (*stack).head = m;
        //@ close stack(stack);
        
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack != 0 &*& stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        //@ open nodes((*stack).head);
        
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