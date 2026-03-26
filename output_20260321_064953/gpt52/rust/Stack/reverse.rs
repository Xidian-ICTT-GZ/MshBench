use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(list<int> vs, *mut Node n) =
    n == std::ptr::null_mut() ?
        vs == nil
    :
        std::alloc::alloc_block(n as *mut u8, Layout::new::<Node>()) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        nodes(?vs0, next) &*&
        vs == cons(v, vs0);

pred stack(*mut Stack s, list<int> vs) =
    std::alloc::alloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    (*s).head |-> ?h &*&
    nodes(vs, h);

@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result == std::ptr::null_mut() ? true : stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(nil, std::ptr::null_mut());
        //@ close stack(stack, nil);
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, cons(value, vs));
    {
        //@ open stack(stack, vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes(cons(value, vs), n);
        (*stack).head = n;
        //@ close stack(stack, cons(value, vs));
        
        
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, cons(?v, ?vs0));
    //@ ens stack(stack, vs0) &*& result == v;
    {
        //@ open stack(stack, cons(v, vs0));
        let head = (*stack).head;
        //@ open nodes(cons(v, vs0), head);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        //@ close stack(stack, vs0);
        result
    }
    
    unsafe fn reverse(stack: *mut Stack)
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, ?vs2);
    {
        //@ open stack(stack, vs);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close nodes(nil, m);
        
        
        loop {
            //@ inv nodes(?vsn, n) &*& nodes(?vsm, m);
            
            if n.is_null() {
                break;
            }
            
            //@ open nodes(vsn, n);
            let next = (*n).next;
            
            (*n).next = m;
            //@ close nodes(cons(?v, vsm), n);
            m = n;
            n = next;
            //@ assert nodes(?vsn2, n);
            //@ assert nodes(?vsm2, m);
            
            
        }
        
        (*stack).head = m;
        //@ close stack(stack, vsm);
        
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, ?vs);
    //@ ens true;
    {
        //@ open stack(stack, vs);
        //@ open nodes(vs, (*stack).head);
        //@ assert false;
        
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()
{
    unsafe {
        let s = Stack::create();
        //@ open stack(s, nil);
        //@ close stack(s, nil);
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);
        
        let result2 = Stack::pop(s);
        
        Stack::dispose(s);
    }
}