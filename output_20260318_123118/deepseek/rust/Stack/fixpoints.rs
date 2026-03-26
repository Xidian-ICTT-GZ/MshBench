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
        (*n).value == v &&
        (*n).next == next &&
        alloc::allocated(n as *mut u8, Layout::new::<Node>())
    }
}

#[predicate]
fn lseg(start: *mut Node, end: *mut Node) -> bool {
    start == end ||
    exists!(next: *mut Node, v: i32) {
        node_own(start, v, next) && lseg(next, end)
    }
}

#[predicate]
fn stack_own(s: *mut Stack) -> bool {
    unsafe {
        exists!(head: *mut Node) {
            (*s).head == head &&
            lseg(head, std::ptr::null_mut()) &&
            alloc::allocated(s as *mut u8, Layout::new::<Stack>())
        }
    }
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
        close lseg(std::ptr::null_mut(), std::ptr::null_mut());
        close stack_own(stack);
        stack
    }
    
    #[requires(stack_own(stack))]
    #[ensures(stack_own(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        open stack_own(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        close node_own(n, value, (*stack).head);
        open lseg((*stack).head, std::ptr::null_mut());
        close lseg(n, std::ptr::null_mut());
        (*stack).head = n;
        close stack_own(stack);
    }
    
    #[requires(stack_own(stack))]
    #[ensures(stack_own(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        open stack_own(stack);
        let head = (*stack).head;
        open lseg(head, std::ptr::null_mut());
        open node_own(head, _, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        close stack_own(stack);
        result
    }

    #[requires(stack_own(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        open stack_own(stack);
        open lseg((*stack).head, std::ptr::null_mut());
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);
        let result2 = Stack::pop(s);
        Stack::dispose(s);
    }
}