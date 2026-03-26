//@ pred stack_node(node: *mut Node, next: *mut Node, value: i32) = (*node).next |-> next &*& (*node).value |-> value;
//@ pred stack(stack: *mut Stack, head: *mut Node) = (*stack).head |-> head;

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
        //@ close stack(stack, std::ptr::null_mut());
        
        
        stack
        //@ ens stack(result, std::ptr::null_mut());
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    
    
    {
        //@ req stack(stack, ?head);
        //@ open stack(stack, head);
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close stack_node(n, head, value);
        (*stack).head = n;
        //@ close stack(stack, n);
        
        
        //@ ens stack(stack, _);
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        //@ req stack(stack, ?head) &*& head != std::ptr::null_mut() &*& stack_node(head, ?next, ?value);
        //@ open stack(stack, head);
        //@ open stack_node(head, next, value);
        
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, next);
        
        result
        //@ ens stack(stack, _) &*& result == value;
    }
    
    unsafe fn reverse(stack: *mut Stack)
    
    
    {
        //@ req stack(stack, ?orig_head);
        //@ open stack(stack, orig_head);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ let mut rev = std::ptr::null_mut();
        //@ let mut remaining = orig_head;
        //@ loop_invariant stack_nodes(remaining, n) &*& stack_nodes_rev(rev, m) &*& stack(stack, _) &*& (*stack).head |-> n;
        //@ open stack_nodes(remaining, n);
        //@ open stack_nodes_rev(rev, m);
        
        loop {
            
            if n.is_null() {
                break;
            }
            
            let next = (*n).next;
            //@ open stack_node(n, next, _);
            
            (*n).next = m;
            //@ close stack_node(n, m, _);
            //@ close stack_nodes_rev(n, n);
            m = n;
            n = next;
            //@ remaining = next;
            //@ rev = n;
            
            
        }
        
        (*stack).head = m;
        //@ close stack(stack, m);
        //@ ens stack(stack, ?new_head) &*& stack_nodes_rev(orig_head, new_head);
    }

    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        //@ req stack(stack, _);
        //@ open stack(stack, _);
        
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
        //@ ens true;
    }

}

//@ pred stack_nodes(h: *mut Node, t: *mut Node) =
//@   h == t ?
//@     emp
//@   :
//@     h != std::ptr::null_mut() &*& stack_node(h, ?next, _) &*& stack_nodes(next, t);
//@ 
//@ pred stack_nodes_rev(h: *mut Node, t: *mut Node) =
//@   h == t ?
//@     emp
//@   :
//@     h != std::ptr::null_mut() &*& stack_node(h, ?prev, _) &*& stack_nodes_rev(prev, t);

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