//@ predicate Nodes(*mut Node head;);

//@ predicate Stack_own(*mut Stack stack; *mut Node head) =
//@   stack |-> ?s &*& struct_Stack_padding(s) &*& s.head |-> head;

//@ predicate Nodes(nil;) = true;
//@ predicate Nodes(cons(?n);) =
//@   n |-> ?node &*& struct_Node_padding(node) &*& node.value |-> _ &*& node.next |-> ?next &*& Nodes(next);

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
    //@ ens Stack_own(result, null);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Stack_own(stack, null);
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack_own(stack, ?old_head) &*& Nodes(old_head);
    //@ ens Stack_own(stack, ?new_head) &*& Nodes(new_head);
    {
        //@ open Stack_own(stack, old_head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n);
        //@ close Stack_own(stack, n);
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack_own(stack, ?head) &*& Nodes(head);
    //@ ens true;
    {
        //@ open Stack_own(stack, _);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}