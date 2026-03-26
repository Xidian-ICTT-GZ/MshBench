//@ pred nodes(*mut Node, list<i32>) = 
//@   match list {
//@     nil => *mut Node == 0,
//@     cons(h, t) => *mut Node != 0 &*& 
//@       struct_Node_padding(*mut Node) &*&
//@       (*mut Node).value |-> h &*&
//@       (*mut Node).next |-> ?next &*&
//@       nodes(next, t)
//@   };
//@ pred stack(*mut Stack, list<i32>) =
//@   *mut Stack != 0 &*&
//@   struct_Stack_padding(*mut Stack) &*&
//@   (*mut Stack).head |-> ?head &*&
//@   nodes(head, list);

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes(nodes, ?vs);
//@ ens nodes(nodes, vs) &*& result == sum(vs);
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open nodes(nodes, _);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close nodes(nodes, _);
    }
    //@ if (nodes == 0) { assert vs == nil; } else { assert vs == cons(?h, ?t); }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, nil);
        
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, vs) &*& result == (vs == nil);
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
        //@ close stack(stack, cons(value, vs));
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, cons(?v, ?vs));
    //@ ens stack(stack, vs) &*& result == v;
    {
        
        let head = (*stack).head;
        //@ open stack(stack, _);
        //@ open nodes(head, _);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, vs);
        
        result
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, ?vs);
    //@ ens true;
    {
        
        let mut n = (*stack).head;
        //@ open stack(stack, _);
        loop {
            
            if n.is_null() {
                break;
            }
            
            let next = (*n).next;
            //@ open nodes(n, _);
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