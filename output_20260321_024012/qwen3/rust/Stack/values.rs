use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred node(n: *mut Node, v: i32, next: *mut Node) = n != 0 &*& struct_Node_padding(n) &*& (*n).next |-> next &*& (*n).value |-> v;
//@ pred stack(s: *mut Stack, head: *mut Node) = s != 0 &*& struct_Stack_padding(s) &*& (*s).head |-> head;

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, 0);
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?old_head) &*& old_head == 0 ? true : node(old_head, _, _);
    //@ ens stack(stack, ?new_head) &*& node(new_head, value, old_head);
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open stack(stack, old_head);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, value, old_head);
        //@ close stack(stack, n);
        
        
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, ?head) &*& head == 0 ? true : node(head, _, _);
    //@ ens true;
    {
        //@ open stack(stack, _);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}