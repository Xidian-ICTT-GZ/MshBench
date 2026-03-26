use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

//@ pred node<n> = n != std::ptr::null_mut() &*& malloc_block_Node(n, 1) &*& 
//@   n->next |-> _ &*& n->value |-> _;

struct Stack {
    head: *mut Node,
}
//@ pred stack(s) = s != std::ptr::null_mut() &*& malloc_block_Stack(s, 1) &*&
//@   s->head |-> _;

impl Stack {

    unsafe fn create() -> *mut Stack
    
    //@ requires true;
    //@ ensures stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }

    unsafe fn get_count(stack: *mut Stack) -> i32
    
    //@ requires stack(stack);
    //@ ensures stack(stack);
    {
        
        let head = (*stack).head;
        
        let mut n = head;
        let mut i = 0;
        
        loop 
        //@ invariant stack(stack) &*& (i >= 0) &*& (n == head || n != std::ptr::null_mut());
        {
            
            if n.is_null() {
                break;
            }
            
            n = (*n).next;
            i += 1;
            
        }
        
        
        
        i
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    
    //@ requires stack(stack) &*& stack(other);
    //@ ensures stack(stack);
    {
        
        
        
        
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        
        if !n.is_null() {
            
            loop 
            //@ invariant n != std::ptr::null_mut();
            {
                

                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
                
                
            }
            
            (*n).next = (*stack).head;
            
            
            (*stack).head = head0;
        }
        
        
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    
    //@ requires stack(stack);
    //@ ensures stack(stack);
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
    
    //@ requires stack(stack) &*& (*stack).head != std::ptr::null_mut();
    //@ ensures stack(stack);
    {
        
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    
    //@ requires stack(stack);
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
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}