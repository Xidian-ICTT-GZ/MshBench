use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

#[predicate]
fn node_list(n: *mut Node) -> bool {
    n.is_null() || (n as usize != 0 && node_list((*n).next))
}

#[predicate]
fn stack_owns(s: *mut Stack) -> bool {
    s as usize != 0 && node_list((*s).head)
}

#[requires(true)]
#[ensures(stack_owns(result))]
unsafe fn Stack_create() -> *mut Stack {
    let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
    if stack.is_null() {
        handle_alloc_error(Layout::new::<Stack>());
    }
    (*stack).head = std::ptr::null_mut();
    stack
}

#[requires(stack_owns(stack))]
#[ensures(stack_owns(stack))]
unsafe fn Stack_push(stack: *mut Stack, value: i32) {
    let n = alloc(Layout::new::<Node>()) as *mut Node;
    if n.is_null() {
        handle_alloc_error(Layout::new::<Node>());
    }
    (*n).next = (*stack).head;
    (*n).value = value;
    (*stack).head = n;
}

#[requires(stack_owns(stack) && !(*stack).head.is_null())]
#[ensures(stack_owns(stack))]
unsafe fn Stack_pop(stack: *mut Stack) -> i32 {
    let head = (*stack).head;
    let result = (*head).value;
    (*stack).head = (*head).next;
    dealloc(head as *mut u8, Layout::new::<Node>());
    result
}

#[requires(stack_owns(stack))]
#[ensures(stack_owns(stack))]
unsafe fn Stack_filter(stack: *mut Stack, p: I32Predicate) {
    filter_nodes(&raw mut (*stack).head, p);
}

#[requires(true)]
#[ensures(true)]
unsafe fn Stack_dispose(stack: *mut Stack) {
    dispose_nodes((*stack).head);
    dealloc(stack as *mut u8, Layout::new::<Stack>());
}

#[requires(true)]
#[ensures(true)]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate) {
    if !(*n).is_null() {
        let keep = p((**n).value);
        if keep {
            filter_nodes(&raw mut (**n).next, p);
        } else {
            let next_ = (**n).next;
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}

#[requires(true)]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

#[requires(true)]
#[ensures(true)]
unsafe fn neq_20(x: i32) -> bool {
    x != 20
}

fn main() {
    unsafe {
        let s = Stack_create();
        Stack_push(s, 10);
        Stack_push(s, 20);
        Stack_filter(s, neq_20);
        Stack_dispose(s);
    }
}