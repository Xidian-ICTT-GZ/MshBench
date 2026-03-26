use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_own(n: *mut Node, v: i32, next: *mut Node) = 
    n != std::ptr::null_mut() &&
    (n as usize) % std::mem::align_of::<Node>() == 0 &&
    (n as usize) != 0;

#[predicate]
fn stack_own(s: *mut Stack, head: *mut Node) = 
    s != std::ptr::null_mut() &&
    (s as usize) % std::mem::align_of::<Stack>() == 0 &&
    (s as usize) != 0;

#[predicate]
fn stack_list(s: *mut Stack) = 
    s != std::ptr::null_mut();

impl Stack {
    #[ensures(stack_own(result, std::ptr::null_mut()))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack_own(stack, _))]
    #[ensures(stack_own(stack, _))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_own(stack, _))]
    #[ensures(stack_own(stack, _))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack_own(stack, _))]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}