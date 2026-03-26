use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ predicate nodes(nodes: *mut Node; result: i32) = 
//@     nodes == 0 ? result == 0 : 
//@     alloc_block(nodes, std::mem::size_of::<Node>()) &*&
//@     struct_Node_padding(nodes) &*&
//@     (*nodes).next |-> ?next &*&
//@     (*nodes).value |-> ?value &*&
//@     nodes(next, ?subsum) &*&
//@     result == value + subsum;

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes(nodes, ?sum);
//@ ens nodes(nodes, sum) &*& result == sum;
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open nodes(nodes, sum);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close nodes(nodes, sum);
    }
    
    result
}

impl Stack {
    //@ predicate stack(stack: *mut Stack) = 
    //@     alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    //@     struct_Stack_padding(stack) &*&
    //@     (*stack).head |-> ?head &*&
    //@     nodes(head, _);

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack);
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        //@ close stack(stack);
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(n, _);
        //@ close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        result
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        let mut n = (*stack).head;
        loop {
            //@ open nodes(n, _);
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