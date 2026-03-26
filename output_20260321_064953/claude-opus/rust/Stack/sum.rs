use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

//@ pred node<n: int>(p: *mut Node) = p |-> Node { next: ?next, value: ?value } &*& node<n-1>(next) &*& n > 0;
//@ pred node<0>(p: *mut Node) = p == std::ptr::null_mut();

struct Stack {
    head: *mut Node,
}

//@ pred stack(p: *mut Stack, n: int) = p |-> Stack { head: ?head } &*& node<n>(head);

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ requires node(?n, nodes);
//@ ensures node(n, nodes) &*& result == (if n > 0 then get_nodes_sum_recursive(nodes) else 0);
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open node(?m, nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close node(m, nodes);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result, 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ requires stack(stack, ?n);
    //@ ensures stack(stack, n);
    {
        
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        
        
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?n);
    //@ ensures stack(stack, n);
    {
        
        let result = get_nodes_sum((*stack).head);
        
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack, ?n);
    //@ ensures stack(stack, n + 1);
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(1 + n, n);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?n) &*& n > 0;
    //@ ensures stack(stack, n - 1);
    {
        
        let head = (*stack).head;
        //@ open node(n, head);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        //@ close node(n - 1, (*stack).head);
        
        result
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack, ?n);
    //@ ensures true;
    {
        
        let mut n = (*stack).head;
        loop {
            //@ if n.is_null() { break; } open node(?m, n);
            
            if n.is_null() {
                break;
            }
            
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}