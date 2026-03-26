use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred node(p: *mut Node; next: *mut Node, value: i32) =
    p != 0 &*&
    std::alloc::alloc_block(p as *mut u8, Layout::new::<Node>()) &*&
    (*p).next |-> next &*&
    (*p).value |-> value;

pred nodes(p: *mut Node) =
    p == 0 ? true : node(p, ?nxt, ?v) &*& nodes(nxt);

pred stack(p: *mut Stack) =
    p != 0 &*&
    std::alloc::alloc_block(p as *mut u8, Layout::new::<Stack>()) &*&
    (*p).head |-> ?h &*& nodes(h);

@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result);
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close stack(stack);
        //@ open stack(stack);
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(std::ptr::null_mut());
        //@ close stack(stack);
        
        
        stack
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
        //@ close node(n, (*stack).head, value);
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ open node(n, (*stack).head, value);
        (*stack).head = n;
        //@ close node(n, (*n).next, (*n).value);
        //@ close nodes(n);
        //@ close stack(stack);
        
        
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
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}