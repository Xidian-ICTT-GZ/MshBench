use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ predicate node(node: *mut Node) =
//@     alloc_block(node, std::mem::size_of::<Node>()) &*&
//@     struct_Node_padding(node) &*&
//@     (*node).next |-> ?next &*&
//@     (*node).value |-> ?value &*&
//@     (next == 0 ? true : node(next));

//@ predicate nodes(node: *mut Node) =
//@     node == 0 ? true :
//@     node(node) &*& nodes((*node).next);

//@ predicate stack(stack: *mut Stack) =
//@     alloc_block(stack, std::mem::size_of::<Stack>()) &*&
//@     struct_Stack_padding(stack) &*&
//@     (*stack).head |-> ?head &*&
//@     nodes(head);

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req nodes(node);
//@ ens nodes(node);
{
    
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes(node);
        //@ open node(node);
        let tail_sum = get_nodes_sum((*node).next);
        //@ close node(node);
        //@ close nodes(node);
        result = (*node).value + tail_sum;
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
        //@ close nodes(0 as *mut Node);
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
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n);
        //@ close nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
        
        
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack);
    
    
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        //@ open node(head);
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