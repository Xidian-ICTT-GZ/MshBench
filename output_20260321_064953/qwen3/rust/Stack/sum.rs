use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

//@ pred node(node: *mut Node, next: *mut Node, value: i32) = (*node).next |-> next &*& (*node).value |-> value;

struct Stack {
    head: *mut Node,
}

//@ pred stack(stack: *mut Stack, head: *mut Node) = (*stack).head |-> head;

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes == null ? true : node(nodes, ?next, ?value) &*& nodes != null &*& [_]is_Send::<Node>();
//@ ens true;
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open node(nodes, ?next, ?value);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close node(nodes, next, value);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, null);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, null);
        
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req stack(stack, ?head);
    //@ ens stack(stack, head) &*& result == (head == null);
    {
        
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        //@ close stack(stack, head);
        
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(stack, ?head);
    //@ ens stack(stack, head);
    {
        
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack, head);
        
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?old_head);
    //@ ens stack(stack, ?new_head);
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n, old_head, value);
        (*stack).head = n;
        //@ close stack(stack, n);
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, ?old_head) &*& old_head != null &*& node(old_head, ?next, ?value);
    //@ ens stack(stack, next) &*& result == value;
    {
        
        let head = (*stack).head;
        //@ open stack(stack, _);
        //@ open node(head, ?next, ?value);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, next);
        
        result
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, ?head);
    //@ ens true;
    {
        //@ open stack(stack, _);
        let mut n = (*stack).head;
        loop {
            
            if n.is_null() {
                break;
            }
            
            let next = (*n).next;
            //@ open node(n, _, _);
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