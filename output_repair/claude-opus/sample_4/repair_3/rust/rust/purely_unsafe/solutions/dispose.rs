use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_owned(n: *mut Node) = n != std::ptr::null_mut();

#[predicate]
fn stack_owned(s: *mut Stack) = s != std::ptr::null_mut();

#[predicate]
fn nodes_chain(n: *mut Node) = 
    n == std::ptr::null_mut() || node_owned(n);

unsafe fn dispose_nodes(n: *mut Node)
#[requires nodes_chain(n)]
#[ensures true]
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires true]
    #[ensures stack_owned(result)]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires stack_owned(stack)]
    #[ensures true]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        result
    }

    #[requires stack_owned(stack)]
    #[ensures stack_owned(stack)]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires stack_owned(stack)]
    #[ensures true]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires stack_owned(stack)]
    #[ensures true]
    unsafe fn dispose(stack: *mut Stack) {
        dispose_nodes((*stack).head);
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