use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(p: *mut Node) =
    p == 0 ?
        true
    :
        (*p).next |-> ?nxt &*& (*p).value |-> ?v &*& nodes(nxt);

pred stack(s: *mut Stack) =
    (*s).head |-> ?h &*& nodes(h);

@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req nodes(node);
//@ ens nodes(node);
{
    
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes(node);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close nodes(node);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result != 0 &*& stack(result);
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
        let old_head = (*stack).head;
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = old_head;
        (*n).value = value;
        (*stack).head = n;
        
        
        //@ close nodes(n);
        //@ close stack(stack);
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack) &*& (*stack).head |-> ?h &*& h != 0;
    //@ ens stack(stack);
    {
        
        //@ open stack(stack);
        let head = (*stack).head;
        
        //@ open nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close stack(stack);
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        //@ open nodes((*stack).head);
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

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