use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_own(n: *mut Node, next: *mut Node, value: i32) = 
    n != std::ptr::null_mut() &&
    (*n).next == next &&
    (*n).value == value;

#[predicate]
fn stack_own(s: *mut Stack, head: *mut Node) = 
    s != std::ptr::null_mut() &&
    (*s).head == head;

#[predicate]
fn stack_list(head: *mut Node) = 
    head == std::ptr::null_mut() ||
    (exists next: *mut Node, value: i32 :: 
        node_own(head, next, value) && stack_list(next));

impl Stack {
    #[ensures(result != std::ptr::null_mut() && stack_own(result, std::ptr::null_mut()) && stack_list(std::ptr::null_mut()))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack_own(stack, ?head) && stack_list(head))]
    #[ensures(exists next: *mut Node :: stack_own(stack, next) && node_own(next, head, value) && stack_list(next))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_own(stack, ?head) && head != std::ptr::null_mut() && exists next: *mut Node, v: i32 :: node_own(head, next, v) && stack_list(next))]
    #[ensures(exists next: *mut Node :: stack_own(stack, next) && stack_list(next))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack_own(stack, ?head) && stack_list(head))]
    #[ensures(true)]
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