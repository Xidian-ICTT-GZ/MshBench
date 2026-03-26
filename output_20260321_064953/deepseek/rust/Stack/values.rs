use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {

    unsafe fn create() -> *mut Stack
    
    //@ req true;
    //@ ens result != 0 as *mut Stack;
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        //@ close nodes(0 as *mut Node);
        //@ close stack_inv(stack);
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    
    //@ req stack_inv(stack);
    //@ ens stack_inv(stack);
    
    {
        //@ open stack_inv(stack);
        //@ open nodes((*stack).head);
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        
        //@ close nodes(n);
        //@ close stack_inv(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
    
    //@ req stack_inv(stack);
    //@ ens true;
    
    {
        //@ open stack_inv(stack);
        //@ open nodes((*stack).head);
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}
//@ predicate nodes(Node *node) = node == 0 as *mut Node ? true : alloc_block(node, std::mem::size_of::<Node>()) &*& struct_Node_padding(node) &*& (*node).next |-> ?next &*& (*node).value |-> ?value &*& nodes(next);
//@ predicate stack_inv(*mut Stack stack) = alloc_block(stack, std::mem::size_of::<Stack>()) &*& struct_Stack_padding(stack) &*& (*stack).head |-> ?head &*& nodes(head);

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}