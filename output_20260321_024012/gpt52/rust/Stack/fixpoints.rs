use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred nodes(list<int> vs, *mut Node p) =
    p == std::ptr::null_mut() ?
        vs == nil
    :
        (*p).next |-> ?nxt &*& (*p).value |-> ?v &*& std::alloc::alloc_block(p as *mut u8, Layout::new::<Node>()) &*& nodes(?vs0, nxt) &*& vs == cons(v, vs0);

pred stack(*mut Stack s, list<int> vs) =
    (*s).head |-> ?h &*& std::alloc::alloc_block(s as *mut u8, Layout::new::<Stack>()) &*& nodes(vs, h);
@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, nil);
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close nodes(nil, std::ptr::null_mut());
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, nil);
        
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, cons(value, vs));
    
    
    {
        //@ open stack(stack, vs);
        //@ open nodes(vs, ?h);
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes(vs, (*stack).head);
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
        //@ close nodes(vs0, (*head).next);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, vs0);
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, nil);
    //@ ens true;
    
    
    {
        
        //@ open stack(stack, nil);
        //@ open nodes(nil, ?h);
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