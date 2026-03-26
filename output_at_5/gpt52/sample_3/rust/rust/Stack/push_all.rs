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
        emp
    } else {
        (*n).next |-> ?nxt &*&
        (*n).value |-> ?v &*&
        alloc_block(n as *mut u8, Layout::new::<Node>()) &*&
        nodes(nxt)
    };

pred stack(s: *mut Stack) =
    (*s).head |-> ?h &*&
    alloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    nodes(h);

@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result);
    
    
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

    unsafe fn get_count(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack);
    
    
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ close stack(stack);
        
        let mut n = head;
        let mut i = 0;
        
        loop {
            
            //@ inv stack(stack) &*& nodes(n);
            if n.is_null() {
                break;
            }
            
            //@ open nodes(n);
            let nxt = (*n).next;
            //@ close nodes(n);
            n = nxt;
            i += 1;
            
        }
        
        
        
        i
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ req stack(stack) &*& stack(other);
    //@ ens stack(stack);
    
    
    {
        //@ open stack(other);
        let head0 = (*other).head;
        //@ open nodes(head0);
        //@ close nodes(head0);
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        
        if !n.is_null() {
            
            loop {
                
                //@ inv stack(stack) &*& nodes(head0) &*& nodes(n) &*& n != 0;
                //@ open nodes(n);

                if (*n).next.is_null() {
                    //@ close nodes(n);
                    break;
                }
                let nxt = (*n).next;
                //@ close nodes(n);
                n = nxt;
                
                
            }
            
            //@ open stack(stack);
            (*n).next = (*stack).head;
            (*stack).head = head0;
            //@ close stack(stack);
        }
        
        
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack);
    //@ ens stack(stack);
    
    
    {
        //@ open stack(stack);
        let old_head = (*stack).head;
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = old_head;
        (*n).value = value;
        //@ close nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack) &*& (*stack).head != std::ptr::null_mut();
    //@ ens stack(stack);
    
    
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close stack(stack);
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
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
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}