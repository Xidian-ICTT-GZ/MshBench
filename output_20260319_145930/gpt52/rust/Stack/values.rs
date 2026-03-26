use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(ptr: *mut Node) =
    ptr == 0 ?
        true
    :
        alloc_block_Node(ptr) &*&
        (*ptr).next |-> ?nxt &*&
        (*ptr).value |-> ?v &*&
        nodes(nxt);

pred stack(ptr: *mut Stack) =
    alloc_block_Stack(ptr) &*&
    (*ptr).head |-> ?h &*&
    nodes(h);

@*/

impl Stack {

    //@ req true;
    //@ ens result != 0 &*& stack(result);
    unsafe fn create() -> *mut Stack
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close stack(stack);
        //@ open stack(stack);
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(0);
        //@ close stack(stack);
        
        
        stack
    }
    
    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32)
    
    
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open stack(stack);
        //@ open nodes((*stack).head);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes((*n).next);
        //@ close nodes(n);
        //@ close stack(stack);
        
        
    }

    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        
        //@ open stack(stack);
        //@ open nodes((*stack).head);
        //@ close nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}