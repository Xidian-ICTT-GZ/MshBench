use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(node: *mut Node) =
    node == 0 ?
        true
    :
        alloc_block(node as *u8, Layout::new::<Node>()) &*&
        (*node).next |-> ?next &*&
        (*node).value |-> ?v &*&
        nodes(next);

pred stack(s: *mut Stack) =
    alloc_block(s as *u8, Layout::new::<Stack>()) &*&
    (*s).head |-> ?h &*&
    nodes(h);

@*/

//@ req nodes(nodes);
//@ ens nodes(nodes) &*& result == 0 ? true : true;
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32

{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open nodes(nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close nodes(nodes);
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
        
        //@ close nodes(0);
        //@ close stack(stack);
        
        stack
    }
    
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == (old((*stack).head) == 0);
    unsafe fn is_empty(stack: *mut Stack) -> bool
    
    
    {
        //@ open stack(stack);
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        
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
        
        //@ close nodes(n);
        //@ close stack(stack);
        
    }

    //@ req stack(stack) &*& (*stack).head != 0;
    //@ ens stack(stack);
    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        //@ close stack(stack);
        
        result
    }
    
    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn popn(stack: *mut Stack, n: i32)
    
    
    {
        let mut i = 0;
        loop {
            //@ inv stack(stack);
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        //@ open stack(stack);
        let mut n = (*stack).head;
        loop {
            //@ inv nodes(n);
            if n.is_null() {
                break;
            }
            
            //@ open nodes(n);
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        //@ open nodes(0);
        
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