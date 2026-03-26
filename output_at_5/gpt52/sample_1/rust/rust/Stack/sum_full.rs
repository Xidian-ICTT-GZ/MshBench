use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(?p; ?vs) =
    if p == std::ptr::null_mut() {
        vs == nil
    } else {
        (*p).next |-> ?nxt &*& (*p).value |-> ?v &*& nodes(nxt; ?vs0) &*& vs == cons(v, vs0)
    };

pred stack(?s; ?vs) =
    (*s).head |-> ?h &*& nodes(h; vs);

@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req nodes(node; ?vs);
//@ ens nodes(node; vs);
{
    
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes(node; vs);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close nodes(node; vs);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result != std::ptr::null_mut() &*& stack(result; nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        //@ close nodes(std::ptr::null_mut(); nil);
        //@ close stack(stack; nil);
        
        stack
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(stack; ?vs);
    //@ ens stack(stack; vs);
    {
        //@ open stack(stack; vs);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack; vs);
        
        result
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack; ?vs);
    //@ ens stack(stack; cons(value, vs));
    {
        //@ open stack(stack; vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        
        //@ close nodes(n; cons(value, vs));
        //@ close stack(stack; cons(value, vs));
        
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack; ?vs) &*& vs != nil;
    //@ ens stack(stack; tail(vs));
    {
        //@ open stack(stack; vs);
        let head = (*stack).head;
        //@ open nodes(head; vs);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close stack(stack; tail(vs));
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack; ?vs);
    //@ ens true;
    {
        //@ open stack(stack; vs);
        //@ open nodes((*stack).head; vs);
        //@ assert false;
        
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let sum = Stack::get_sum(s);
        
        let result1 = Stack::pop(s);
        
        let result2 = Stack::pop(s);
        
        Stack::dispose(s);
    }
}