use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(?head; int count) =
    head == 0 ?
        count == 0
    :
        count > 0 &*&
        (*head).next |-> ?n &*&
        (*head).value |-> _ &*&
        nodes(n, count - 1);

pred stack(?s; int count) =
    (*s).head |-> ?h &*& nodes(h, count);

@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result == 0 ? true : stack(result, 0);
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close nodes(0, 0);
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, 0);
        
        
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?count);
    //@ ens stack(stack, count + 1);
    
    
    {
        //@ open stack(stack, count);
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes(n, count + 1);
        (*stack).head = n;
        //@ close stack(stack, count + 1);
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, ?count) &*& count > 0;
    //@ ens stack(stack, count - 1);
    
    
    {
        //@ open stack(stack, count);
        
        let head = (*stack).head;
        //@ open nodes(head, count);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close stack(stack, count - 1);
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, ?count);
    //@ ens true;
    
    
    {
        //@ open stack(stack, count);
        //@ open nodes((*stack).head, count);
        
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()

{
    unsafe {
        let s = Stack::create();
        //@ assert stack(s, 0);
        Stack::push(s, 10);
        //@ assert stack(s, 1);
        Stack::push(s, 20);
        //@ assert stack(s, 2);
        Stack::pop(s);
        //@ assert stack(s, 1);
        Stack::pop(s);
        //@ assert stack(s, 0);
        Stack::dispose(s);
    }
}