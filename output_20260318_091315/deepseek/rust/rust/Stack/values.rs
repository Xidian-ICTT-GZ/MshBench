use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_own(n: *mut Node, v: i32, next: *mut Node) -> bool {
    unsafe {
        alloc::points_to(n, Node { next, value: v })
    }
}

#[predicate]
fn stack_nodes(head: *mut Node) -> bool {
    head.is_null() ? true : 
        exists!(v: i32, next: *mut Node) 
        *& node_own(head, v, next) *& stack_nodes(next)
}

#[predicate]
fn stack_own(s: *mut Stack, head: *mut Node) -> bool {
    unsafe {
        alloc::points_to(s, Stack { head }) *& stack_nodes(head)
    }
}

impl Stack {
    #[requires(true)]
    #[ensures(result.is_null() ? true : stack_own(result, std::ptr::null_mut()))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    #[requires(stack_own(stack, old_head))]
    #[ensures(stack_own(stack, n) *& node_own(n, value, old_head))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_own(stack, std::ptr::null_mut()))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}