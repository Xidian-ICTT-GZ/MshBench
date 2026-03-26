use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Nodes(node: *mut Node; count: i32) =
    if node == 0 as *mut Node {
        count == 0
    } else {
        alloc_block_Node(node) &*&
        (*node).next |-> ?next &*&
        (*node).value |-> ?value &*&
        Nodes(next, ?tail_count) &*&
        count == tail_count + 1
    };

pred Stack(stack: *mut Stack; count: i32) =
    alloc_block_Stack(stack) &*&
    (*stack).head |-> ?head &*&
    Nodes(head, count);

@*/

//@ req Nodes(node, ?count);
//@ ens Nodes(node, count);
unsafe fn get_nodes_sum(node: *mut Node) -> i32
{
    //@ open Nodes(node, count);
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }
    //@ close Nodes(node, count);
    result
}

impl Stack {

    //@ req true;
    //@ ens Stack(result, 0);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0 as *mut Node, 0);
        //@ close Stack(stack, 0);
        stack
    }
    
    //@ req Stack(stack, ?count);
    //@ ens Stack(stack, count);
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        //@ open Stack(stack, count);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack(stack, count);
        result
    }
    
    //@ req Stack(stack, ?count);
    //@ ens Stack(stack, count + 1);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open Stack(stack, count);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, count + 1);
        //@ close Stack(stack, count + 1);
    }
    
    //@ req Stack(stack, ?count) &*& count > 0;
    //@ ens Stack(stack, count - 1);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open Stack(stack, count);
        let head = (*stack).head;
        //@ open Nodes(head, count);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack, count - 1);
        result
    }

    //@ req Stack(stack, 0);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open Stack(stack, 0);
        //@ open Nodes(_, 0);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

//@ req true;
//@ ens true;
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