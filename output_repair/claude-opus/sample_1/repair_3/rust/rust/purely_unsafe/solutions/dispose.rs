use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(n: *mut Node) =
    n.is_null() ? true : (
        n as usize != 0 &&
        Owned(n) &&
        Owned((*n).next) &&
        node_list((*n).next)
    );

#[requires(node_list(n))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

#[ensures(Owned(result) && result as usize != 0 && Owned((*result).head) && (*result).head.is_null())]
unsafe fn create() -> *mut Stack {
    let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
    if stack.is_null() {
        handle_alloc_error(Layout::new::<Stack>());
    }
    (*stack).head = std::ptr::null_mut();

    return stack;
}

#[requires(Owned(stack) && stack as usize != 0 && Owned((*stack).head))]
#[ensures(true)]
unsafe fn is_empty(stack: *mut Stack) -> bool {
    let head = (*stack).head;

    let result = (*stack).head.is_null();

    return result;
}

#[requires(Owned(stack) && stack as usize != 0 && Owned((*stack).head) && node_list((*stack).head))]
#[ensures(Owned(stack) && stack as usize != 0 && Owned((*stack).head) && node_list((*stack).head))]
unsafe fn push(stack: *mut Stack, value: i32) {
    let n = alloc(Layout::new::<Node>()) as *mut Node;
    if n.is_null() {
        handle_alloc_error(Layout::new::<Node>());
    }
    (*n).next = (*stack).head;
    (*n).value = value;
    (*stack).head = n;
}

#[requires(Owned(stack) && stack as usize != 0 && Owned((*stack).head) && node_list((*stack).head) && !(*stack).head.is_null())]
#[ensures(Owned(stack) && stack as usize != 0 && Owned((*stack).head) && node_list((*stack).head))]
unsafe fn pop(stack: *mut Stack) -> i32 {
    let head = (*stack).head;

    let result = (*head).value;
    (*stack).head = (*head).next;
    dealloc(head as *mut u8, Layout::new::<Node>());

    return result;
}

#[requires(Owned(stack) && stack as usize != 0 && Owned((*stack).head) && node_list((*stack).head))]
#[ensures(true)]
unsafe fn dispose(stack: *mut Stack) {
    dispose_nodes((*stack).head);
    dealloc(stack as *mut u8, Layout::new::<Stack>());
}

impl Stack {
    #[ensures(Owned(result) && result as usize != 0 && Owned((*result).head) && (*result).head.is_null())]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        return stack;
    }

    #[requires(Owned(stack) && stack as usize != 0 && Owned((*stack).head))]
    #[ensures(true)]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        return result;
    }

    #[requires(Owned(stack) && stack as usize != 0 && Owned((*stack).head) && node_list((*stack).head))]
    #[ensures(Owned(stack) && stack as usize != 0 && Owned((*stack).head) && node_list((*stack).head))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(Owned(stack) && stack as usize != 0 && Owned((*stack).head) && node_list((*stack).head) && !(*stack).head.is_null())]
    #[ensures(Owned(stack) && stack as usize != 0 && Owned((*stack).head) && node_list((*stack).head))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        return result;
    }

    #[requires(Owned(stack) && stack as usize != 0 && Owned((*stack).head) && node_list((*stack).head))]
    #[ensures(true)]
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