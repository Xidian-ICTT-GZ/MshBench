use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes_list(n: *mut Node) =
    n == std::ptr::null_mut() ?
        true
    :
        std::alloc::alloc_block(n as *mut u8, Layout::new::<Node>()) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        nodes_list(next);

pred stack(s: *mut Stack) =
    std::alloc::alloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    (*s).head |-> ?h &*&
    nodes_list(h);

@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result == std::ptr::null_mut() ? true : stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close nodes_list(std::ptr::null_mut());
        //@ close stack(stack);
        (*stack).head = std::ptr::null_mut();
        
        
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
            //@ inv stack(stack) &*& nodes_list(n);
            
            if n.is_null() {
                break;
            }
            //@ open nodes_list(n);
            n = (*n).next;
            i += 1;
            //@ close nodes_list(_);
            
        }
        
        
        
        i
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ req stack(stack) &*& stack(other);
    //@ ens stack(stack);
    {
        //@ open stack(other);
        let head0 = (*other).head;
        //@ open nodes_list(head0);
        //@ close nodes_list(head0);
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        
        if !n.is_null() {
            
            loop {
                //@ inv stack(stack) &*& nodes_list(head0) &*& n != std::ptr::null_mut();
                //@ open nodes_list(n);

                if (*n).next.is_null() {
                    //@ close nodes_list(n);
                    break;
                }
                let next = (*n).next;
                //@ close nodes_list(n);
                n = next;
                
                
            }
            
            //@ open stack(stack);
            //@ open nodes_list(n);
            (*n).next = (*stack).head;
            //@ close nodes_list(n);
            
            
            (*stack).head = head0;
            //@ close stack(stack);
        }
        
        
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
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes_list((*n).next);
        //@ close nodes_list(n);
        (*stack).head = n;
        //@ close stack(stack);
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack) &*& (*stack).head |-> ?h &*& h != std::ptr::null_mut();
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes_list(head);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close nodes_list((*stack).head);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        //@ open nodes_list((*stack).head);
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