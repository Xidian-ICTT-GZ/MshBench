//@ pred stack_node(node: *mut Node; next: *mut Node, value: i32) = (*node).next |-> next &*& (*node).value |-> value;
//@ pred stack(stack: *mut Stack; nodes: list<*mut Node>) =
//@   match nodes with
//@   | nil => (*stack).head |-> null
//@   | cons(h, t) => (*stack).head |-> h &*& stack_node(h, ?next, ?v) &*& stack_nodes(next, t)
//@ ;
//@ pred stack_nodes(node: *mut Node, nodes: list<*mut Node>) =
//@   match nodes with
//@   | nil => node == null
//@   | cons(h, t) => node == h &*& stack_node(h, ?next, ?v) &*& stack_nodes(next, t)
//@ ;

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {

    unsafe fn create() -> *mut Stack
    
    
    {
        //@ req true;
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, nil);
        
        
        //@ ens stack(result, nil);
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    
    
    {
        //@ req stack(stack, ?nodes);
        //@ open stack(stack, nodes);
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close stack_node(n, (*stack).head, value);
        //@ close stack(stack, cons(n, nodes));
        
        
        //@ ens stack(stack, cons(n, nodes));
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        //@ req stack(stack, ?nodes) &*& nodes != nil;
        //@ open stack(stack, nodes);
        //@ open stack_nodes(?head, nodes);
        //@ assert nodes == cons(head, ?rest);
        //@ open stack_node(head, ?next, ?v);
        
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, rest);
        
        //@ ens stack(stack, rest) &*& result == v;
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        //@ req stack(stack, nil);
        //@ open stack(stack, nil);
        
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
        //@ ens true;
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