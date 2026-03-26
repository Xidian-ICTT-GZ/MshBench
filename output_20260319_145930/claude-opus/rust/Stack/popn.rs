use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred Nodes(n: *mut Node, count: i32) =
    if n == 0 {
        count == 0
    } else {
        alloc_block_Node(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?value &*&
        Nodes(next, ?rest_count) &*&
        count == rest_count + 1
    };

pred Stack(s: *mut Stack, count: i32) =
    alloc_block_Stack(s) &*&
    (*s).head |-> ?head &*&
    Nodes(head, count);

@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req Nodes(nodes, ?count);
//@ ens Nodes(nodes, count);
{
    let mut result = 0;
    //@ open Nodes(nodes, count);
    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }
    //@ close Nodes(nodes, count);
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack(result, 0);
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
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req Stack(stack, ?count);
    //@ ens Stack(stack, count) &*& result == (count == 0);
    {
        //@ open Stack(stack, count);
        let head = (*stack).head;
        //@ open Nodes(head, count);
        let result = (*stack).head.is_null();
        //@ close Nodes(head, count);
        //@ close Stack(stack, count);
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?count);
    //@ ens Stack(stack, count);
    {
        //@ open Stack(stack, count);
        let result = get_nodes_sum((*stack).head);
        //@ close Stack(stack, count);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack(stack, ?count);
    //@ ens Stack(stack, count + 1);
    {
        //@ open Stack(stack, count);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Nodes(n, count + 1);
        (*stack).head = n;
        //@ close Stack(stack, count + 1);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack(stack, ?count) &*& count > 0;
    //@ ens Stack(stack, count - 1);
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
    
    unsafe fn popn(stack: *mut Stack, n: i32)
    //@ req Stack(stack, ?count) &*& n >= 0 &*& n <= count;
    //@ ens Stack(stack, count - n);
    {
        let mut i = 0;
        loop {
            //@ inv Stack(stack, count - i) &*& i >= 0 &*& i <= n;
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack, ?count);
    //@ ens true;
    {
        //@ open Stack(stack, count);
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