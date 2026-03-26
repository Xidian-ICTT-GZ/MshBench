use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Nodes(n: *mut Node; count: i32) =
    if n == 0 as *mut Node {
        count == 0
    } else {
        alloc_block_Node(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?value &*&
        Nodes(next, ?rest_count) &*&
        count == rest_count + 1
    };

pred Stack(s: *mut Stack;) =
    alloc_block_Stack(s) &*&
    (*s).head |-> ?head &*&
    Nodes(head, _);

@*/

//@ req Nodes(nodes, ?count);
//@ ens Nodes(nodes, count);
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
{
    //@ open Nodes(nodes, count);
    let mut result = 0;
    
    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }
    
    //@ close Nodes(nodes, count);
    result
}

impl Stack {

    //@ req true;
    //@ ens Stack(result);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        //@ close Nodes(0 as *mut Node, 0);
        //@ close Stack(stack);
        stack
    }
    
    //@ req Stack(stack);
    //@ ens Stack(stack);
    unsafe fn is_empty(stack: *mut Stack) -> bool
    {
        //@ open Stack(stack);
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        
        //@ close Stack(stack);
        result
    }
    
    //@ req Stack(stack);
    //@ ens Stack(stack);
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        //@ open Stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack(stack);
        result
    }

    //@ req Stack(stack);
    //@ ens Stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open Stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Nodes(n, _);
        (*stack).head = n;
        
        //@ close Stack(stack);
    }

    //@ req Stack(stack) &*& (*stack).head |-> ?head &*& head != 0 as *mut Node;
    //@ ens Stack(stack);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open Stack(stack);
        let head = (*stack).head;
        //@ open Nodes(head, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack);
        result
    }
    
    //@ req Stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open Stack(stack);
        let mut n = (*stack).head;
        loop {
            //@ inv Nodes(n, _);
            //@ open Nodes(n, _);
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
        //@ open Stack(s);
        //@ open Nodes((*s).head, _);
        //@ close Nodes((*s).head, _);
        //@ close Stack(s);
        Stack::pop(s);
        //@ open Stack(s);
        //@ open Nodes((*s).head, _);
        //@ close Nodes((*s).head, _);
        //@ close Stack(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}