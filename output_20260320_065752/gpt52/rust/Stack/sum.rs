use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes_list(nodes: *mut Node) =
    nodes == std::ptr::null_mut() ?
        true
    :
        alloc_block_Node(nodes) &*&
        (*nodes).next |-> ?next &*&
        (*nodes).value |-> ?v &*&
        nodes_list(next);

pred stack(stack: *mut Stack) =
    alloc_block_Stack(stack) &*&
    (*stack).head |-> ?head &*&
    nodes_list(head);

@*/

//@ req true;
//@ ens true;
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
{
    let mut result = 0;
    
    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }
    
    result
}

impl Stack {

    //@ req true;
    //@ ens stack(result);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        //@ close nodes_list(std::ptr::null_mut());
        //@ close stack(stack);
        stack
    }
    
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == ((*stack).head == std::ptr::null_mut());
    unsafe fn is_empty(stack: *mut Stack) -> bool
    {
        //@ open stack(stack);
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        
        //@ assert result == (head == std::ptr::null_mut());
        //@ close stack(stack);
        result
    }
    
    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        //@ open stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack);
        result
    }

    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        
        //@ close nodes_list((*n).next);
        //@ close nodes_list(n);
        //@ close stack(stack);
    }

    //@ req stack(stack) &*& (*stack).head != std::ptr::null_mut();
    //@ ens stack(stack);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes_list(head);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        //@ close stack(stack);
        result
    }
    
    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack);
        let mut n = (*stack).head;
        loop {
            //@ inv nodes_list(n);
            if n.is_null() {
                break;
            }
            //@ open nodes_list(n);
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        //@ open nodes_list(std::ptr::null_mut());
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