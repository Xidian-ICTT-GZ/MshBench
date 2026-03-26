use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes_list(n: *mut Node) =
    n == std::ptr::null_mut() ?
        true
    :
        std::alloc::alloc_block(n as *mut u8, Layout::new::<Node>()) &*&
        struct_Node_padding(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?value &*&
        nodes_list(next);

pred stack(s: *mut Stack) =
    std::alloc::alloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> ?head &*&
    nodes_list(head);

@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes_list(nodes);
//@ ens nodes_list(nodes);
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open nodes_list(nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close nodes_list(nodes);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result);
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
        
        //@ close nodes_list((*n).next);
        //@ close nodes_list(n);
        //@ close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack) &*& (*stack).head |-> ?h &*& h != std::ptr::null_mut();
    //@ ens stack(stack);
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
    
    unsafe fn popn(stack: *mut Stack, n: i32)
    //@ req true;
    //@ ens true;
    {
        let mut i = 0;
        loop {
            
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
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

fn main()
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