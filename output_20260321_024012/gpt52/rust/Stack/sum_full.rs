use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@
//@ pred nodes_list(n: *mut Node) =
//@     if n == 0 {
//@         true
//@     } else {
//@         (*n).next |-> ?next &*& (*n).value |-> ?v &*& std::alloc::alloc_block(n as *mut u8, Layout::new::<Node>()) &*& nodes_list(next)
//@     };
//@
//@ pred stack(s: *mut Stack) =
//@     (*s).head |-> ?h &*& std::alloc::alloc_block(s as *mut u8, Layout::new::<Stack>()) &*& nodes_list(h);
//@

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req nodes_list(node);
//@ ens nodes_list(node);
{
    //@ open nodes_list(node);
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }
    //@ close nodes_list(node);
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
        //@ close nodes_list(0);
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
        //@ open nodes_list((*stack).head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes_list(n);
        //@ close stack(stack);
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack) &*& (*stack).head |-> ?h &*& h != 0;
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        //@ open nodes_list((*stack).head);
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open nodes_list((*head).next);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close nodes_list((*stack).head);
        //@ close stack(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        //@ open nodes_list((*stack).head);
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