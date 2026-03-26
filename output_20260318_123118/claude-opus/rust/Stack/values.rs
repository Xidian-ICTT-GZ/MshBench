use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate nodes_list(*node: *mut Node; list: list<i32>) = 
    node != std::ptr::null_mut() ?
        node |-> Node{ next: ?next, value: ?v }
        &*& malloc_block<Node>(node)
        &*& nodes_list(next, ?rest)
        &*& list == cons(v, rest)
    :
        list == nil
    ;

predicate stack(struct_ptr: *mut Stack; list: list<i32>) =
    struct_ptr |-> Stack { head: ?h }
    &*& malloc_block<Stack>(struct_ptr)
    &*& nodes_list(h, list)
    ;

impl Stack {

    #[requires(true)]
    #[ensures stack(result, nil)]
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }
    
    #[requires(stack: stack(list))]
    #[ensures(stack: stack(stack, cons(value, list)))]
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack: stack(nil))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
    {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}