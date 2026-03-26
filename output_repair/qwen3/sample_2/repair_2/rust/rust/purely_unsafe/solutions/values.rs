use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_own(n: *mut Node) -> bool {
    n != null_mut() &*& points_to(n as *mut u8, std::mem::size_of::<*mut Node>()) &*&
    points_to((n as usize + std::mem::size_of::<*mut Node>()) as *mut u8, std::mem::size_of::<i32>())
}

#[predicate]
fn stack_own(s: *mut Stack) -> bool {
    s != null_mut() &*& points_to(s as *mut u8, std::mem::size_of::<Stack>())
}

#[predicate]
fn node_list(n: *mut Node) -> bool {
    if n == null_mut() {
        true
    } else {
        unsafe { node_own(n) &*& node_list((*n).next) }
    }
}

#[predicate]
fn stack_valid(s: *mut Stack) -> bool {
    unsafe { stack_own(s) &*& node_list((*s).head) }
}

impl Stack {
    #[ensures(stack_valid(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(stack_valid(stack))]
    #[ensures(stack_valid(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_valid(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}