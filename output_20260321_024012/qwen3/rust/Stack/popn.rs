//@ pred nodes(*mut Node node, list<i32> values) =
//@   match values {
//@     [] => node == 0,
//@     ?v :: ?vs => node != 0 && (*node).value |-> v && (*node).next |-> ?next && nodes(next, vs)
//@   };
//@ pred stack(*mut Stack s, list<i32> values) =
//@   s != 0 && (*s).head |-> ?head && nodes(head, values);

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes(?vs);
//@ ens nodes(vs) &*& result == sum(vs);
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open nodes(_);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close nodes(_);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, []);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(0, []);
        //@ close stack(stack, []);
        
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, vs) &*& result == (vs == []);
    {
        
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        
        
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, vs) &*& result == sum(vs);
    {
        
        let result = get_nodes_sum((*stack).head);
        
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, cons(value, vs));
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(n, cons(value, vs));
        //@ close stack(stack, _);
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, ?vs) &*& vs != [];
    //@ ens stack(stack, tail(vs)) &*& result == head(vs);
    {
        
        let head = (*stack).head;
        //@ open stack(_, _);
        //@ open nodes(_, _);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, _);
        
        result
    }
    
    unsafe fn popn(stack: *mut Stack, n: i32)
    //@ req stack(stack, ?vs) &*& n >= 0 &*& length(vs) >= n;
    //@ ens stack(stack, drop(n, vs));
    {
        let mut i = 0;
        loop {
            
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, _);
    //@ ens true;
    {
        
        let mut n = (*stack).head;
        //@ open stack(_, _);
        loop {
            
            if n.is_null() {
                break;
            }
            
            let next = (*n).next;
            //@ open nodes(_, _);
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()
//@ req true;
//@ ens true;
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