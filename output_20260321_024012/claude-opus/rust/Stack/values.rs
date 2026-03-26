use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

//@ pred node<node_ptr>(node_ptr) =
//@   node_ptr != std::ptr::null_mut() &*&
//@   malloc_block_node(node_ptr) &*&
//@   *node_ptr |-> _ &*&
//@   (*node_ptr).next |-> _ &*&
//@   (*node_ptr).value |-> _;
//@ pred stack<stack_ptr>(stack_ptr) =
//@   malloc_block_stack(stack_ptr) &*&
//@   (*stack_ptr).head |-> ?head &*& (head == std::ptr::null_mut() ? true : node<head>(head));
//@ fixpoint bool malloc_block_node(void* p) { true }
//@ fixpoint bool malloc_block_stack(void* p) { true }

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack);
    //@ ensures stack(stack);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;

    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack);
    //@ ensures true;
    {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}