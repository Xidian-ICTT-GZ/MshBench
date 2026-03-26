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
    //@ ens ptr::nonnull(result) &*& struct_Stack_pat(result) &*& result->head |-> ?h &*& h == 0;
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close struct_Stack_pat(stack);
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req struct_Stack_pat(stack) &*& stack->head |-> ?old_head;
    //@ ens struct_Stack_pat(stack) &*& stack->head |-> ?new_head &*& new_head != 0 &*& struct_Node_pat(new_head) &*& new_head->next |-> old_head &*& new_head->value |-> value;
    {
        //@ open struct_Stack_pat(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close struct_Node_pat(n);
        //@ close struct_Stack_pat(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req struct_Stack_pat(stack) &*& stack->head |-> ?h &*& h == 0;
    //@ ens true;
    {
        //@ open struct_Stack_pat(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}