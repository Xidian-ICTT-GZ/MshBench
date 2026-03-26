//@ predicate Nodes(*mut Node node; i32 sum;) =
//@   node == std::ptr::null_mut::<Node>() ?
//@     sum == 0
//@   :
//@     (*node).next |-> ?next &*& (*node).value |-> ?value &*& Nodes(next, ?tail_sum) &*& sum == value + tail_sum;

//@ predicate StackP(*mut Stack stack; *mut Node head;) =
//@   stack |-> ?s &*& s.head |-> head;

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req Nodes(node, ?sum);
//@ ens Nodes(node, sum) &*& result == sum;
{
    
    let mut result = 0;
    if !node.is_null() {
        //@ open Nodes(node, _);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close Nodes(node, result);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens StackP(result, std::ptr::null_mut::<Node>());
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close StackP(stack, std::ptr::null_mut());
        
        stack
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req StackP(stack, ?head) &*& Nodes(head, ?sum);
    //@ ens StackP(stack, head) &*& Nodes(head, sum) &*& result == sum;
    {
        
        let result = get_nodes_sum((*stack).head);
        
        result
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req StackP(stack, ?old_head) &*& Nodes(old_head, ?old_sum);
    //@ ens StackP(stack, ?new_head) &*& Nodes(new_head, ?new_sum) &*& new_sum == value + old_sum;
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Nodes(n, value + old_sum);
        (*stack).head = n;
        //@ close StackP(stack, n);
        
        
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req StackP(stack, ?head) &*& head != std::ptr::null_mut::<Node>() &*& Nodes(head, ?sum);
    //@ ens StackP(stack, ?new_head) &*& Nodes(new_head, ?new_sum) &*& old_sum == result + new_sum;
    {
        
        let head = (*stack).head;
        //@ open StackP(stack, head);
        //@ open Nodes(head, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close StackP(stack, (*stack).head);
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req StackP(stack, ?head) &*& Nodes(head, _);
    //@ ens true;
    {
        //@ open StackP(stack, _);
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
        let sum = Stack::get_sum(s);
        
        let result1 = Stack::pop(s);
        
        let result2 = Stack::pop(s);
        
        Stack::dispose(s);
    }
}