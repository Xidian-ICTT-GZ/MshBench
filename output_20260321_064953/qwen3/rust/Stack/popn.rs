//@ predicate Nodes(*mut Node nodes; i32 sum) =
//@   nodes == null ? sum == 0 :
//@   exists<Node>(nodes, ?next, ?value) &*& Nodes(next, ?sum1) &*& sum == sum1 + value;

//@ predicate StackPred(*mut Stack stack; *mut Node head) =
//@   exists<Stack>(stack, head);

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req Nodes(nodes, ?sum);
//@ ens Nodes(nodes, sum) &*& result == sum;
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open Nodes(nodes, _);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close Nodes(nodes, result);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens StackPred(result, null);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close StackPred(stack, null);
        
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req StackPred(stack, ?head);
    //@ ens StackPred(stack, head) &*& result == (head == null);
    {
        
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        
        
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req StackPred(stack, ?head) &*& Nodes(head, ?sum);
    //@ ens StackPred(stack, head) &*& Nodes(head, sum) &*& result == sum;
    {
        
        let result = get_nodes_sum((*stack).head);
        
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req StackPred(stack, ?old_head) &*& Nodes(old_head, ?old_sum);
    //@ ens StackPred(stack, ?new_head) &*& Nodes(new_head, old_sum + value);
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, old_sum + value);
        //@ open StackPred(stack, _);
        //@ close StackPred(stack, n);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req StackPred(stack, ?head) &*& head != null &*& Nodes(head, ?sum);
    //@ ens StackPred(stack, ?new_head) &*& Nodes(new_head, ?new_sum) &*& result + new_sum == sum;
    {
        
        let head = (*stack).head;
        //@ open Nodes(head, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close StackPred(stack, (*stack).head);
        
        result
    }
    
    unsafe fn popn(stack: *mut Stack, n: i32)
    //@ req StackPred(stack, ?head) &*& Nodes(head, ?sum) &*& n >= 0;
    //@ ens StackPred(stack, ?new_head) &*& Nodes(new_head, ?new_sum);
    {
        let mut i = 0;
        loop {
            //@ open StackPred(stack, _);
            //@ open Nodes(_, _);
            
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
            //@ close StackPred(stack, _);
        }
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req StackPred(stack, ?head) &*& Nodes(head, _);
    //@ ens true;
    {
        
        let mut n = (*stack).head;
        loop {
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