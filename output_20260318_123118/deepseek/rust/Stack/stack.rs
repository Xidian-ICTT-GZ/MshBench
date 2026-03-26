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
    struct Node { next: *mut Node, value: i32 } &&
    addr_of!((*n).value) != addr_of!((*n).next) &&
    (*n).value == v && (*n).next == next
}

#[predicate]
fn lseg(start: *mut Node, end: *mut Node) -> bool {
    start == end ||
    exists!(next: *mut Node, v: i32) node_own(start, v, next) * lseg(next, end)
}

#[predicate]
fn stack_own(s: *mut Stack) -> bool {
    struct Stack { head: *mut Node } &&
    exists!(head: *mut Node) (*s).head == head && lseg(head, std::ptr::null_mut())
}

impl Stack {
    #[requires(true)]
    #[ensures(stack_own(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(stack_own(stack))]
    #[ensures(stack_own(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_own(stack) && (*stack).head != std::ptr::null_mut())]
    #[ensures(stack_own(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(stack_own(stack))]
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