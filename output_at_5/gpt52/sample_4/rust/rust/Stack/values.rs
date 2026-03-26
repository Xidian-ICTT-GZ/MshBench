use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred node(n: *mut Node; next: *mut Node, value: i32) =
    n != 0 &*&
    n->next |-> next &*&
    n->value |-> value;

pred stack(s: *mut Stack; head: *mut Node) =
    s != 0 &*&
    s->head |-> head;
@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result != 0 &*& stack(result, _);
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close stack(stack, _);
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?head);
    //@ ens stack(stack, _);
    
    
    {
        //@ open stack(stack, head);
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close node(n, _, _);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close stack(stack, n);
        
        
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, _);
    //@ ens true;
    
    
    {
        //@ open stack(stack, _);
        
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}