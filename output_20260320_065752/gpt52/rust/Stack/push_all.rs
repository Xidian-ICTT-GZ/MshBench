use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(n: *mut Node) =
    if n == 0 {
        true
    } else {
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        alloc_block(n as *u8, Layout::new::<Node>()) &*&
        nodes(next)
    };

pred stack(s: *mut Stack) =
    (*s).head |-> ?h &*&
    alloc_block(s as *u8, Layout::new::<Stack>()) &*&
    nodes(h);

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
        //@ close nodes(0);
        //@ close stack(stack);
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }

    //@ req stack(stack);
    //@ ens stack(stack) &*& result >= 0;
    unsafe fn get_count(stack: *mut Stack) -> i32
    
    
    {
        //@ open stack(stack);
        let head = (*stack).head;
        
        let mut n = head;
        let mut i = 0;
        
        //@ close nodes(head);
        //@ close stack(stack);
        loop {
            //@ inv stack(stack) &*& nodes(n) &*& i >= 0;
            
            if n.is_null() {
                break;
            }
            //@ open nodes(n);
            n = (*n).next;
            i += 1;
            //@ close nodes(n);
            
        }
        
        //@ open nodes(n);
        //@ close nodes(0);
        
        i
    }

    //@ req stack(stack) &*& stack(other);
    //@ ens stack(stack);
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    
    
    {
        //@ open stack(other);
        //@ open stack(stack);
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        
        //@ close nodes(head0);
        if !n.is_null() {
            //@ open nodes(n);
            //@ close nodes(n);
            loop {
                //@ inv nodes(head0) &*& nodes(n) &*& n != 0 &*& stack(stack);
                
                if (*n).next.is_null() {
                    break;
                }
                //@ open nodes(n);
                n = (*n).next;
                //@ close nodes(n);
                
                
            }
            
            //@ open nodes(n);
            (*n).next = (*stack).head;
            //@ close nodes(n);
            
            
            (*stack).head = head0;
        }
        
        //@ close stack(stack);
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
        //@ close nodes((*stack).head);
        //@ close nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
        
        
    }

    //@ req stack(stack) &*& (*stack).head != 0;
    //@ ens stack(stack);
    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close nodes((*stack).head);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        
        result
    }

    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        //@ open stack(stack);
        //@ open nodes((*stack).head);
        //@ close nodes((*stack).head); // leak nodes; only dispose stack block
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