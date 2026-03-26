use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[verifast::predicate]
pub fn node_own(n: *mut Node) -> bool {
    std::ptr::points_to(n as *mut u8, std::mem::size_of::<*mut Node>()) &*&
    std::ptr::points_to((n as usize + std::mem::size_of::<*mut Node>()) as *mut u8, std::mem::size_of::<i32>())
}

#[verifast::predicate]
pub fn stack_own(s: *mut Stack) -> bool {
    std::ptr::points_to(s as *mut u8, std::mem::size_of::<*mut Node>())
}

#[verifast::predicate]
pub fn node_list(n: *mut Node) -> bool {
    if n.is_null() { 
        true 
    } else { 
        node_own(n) &*& node_list(unsafe { (*n).next }) 
    }
}

#[verifast::predicate]
pub fn stack_valid(s: *mut Stack) -> bool {
    stack_own(s) &*& node_list(unsafe { (*s).head })
}

impl Stack {
    #[verifast::ensures(stack_valid(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[verifast::requires(stack_valid(stack))]
    #[verifast::ensures(stack_valid(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[verifast::requires(stack_valid(stack))]
    #[verifast::ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}