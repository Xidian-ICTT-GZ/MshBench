use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn nodes(nodes: *mut Node) -> bool {
    if nodes.is_null() {
        true
    } else {
        let node = unsafe { &*nodes };
        nodes(node.next) && true
    }
}

#[predicate]
fn node_owned(nodes: *mut Node) -> bool {
    if nodes.is_null() {
        true
    } else {
        let node = unsafe { &*nodes };
        node_owned(node.next) && true
    }
}

#[predicate]
fn stack(stack: *mut Stack) -> bool {
    if stack.is_null() {
        false
    } else {
        let s = unsafe { &*stack };
        nodes(s.head) && true
    }
}

#[predicate]
fn stack_owned(stack: *mut Stack) -> bool {
    if stack.is_null() {
        false
    } else {
        let s = unsafe { &*stack };
        node_owned(s.head) && true
    }
}

#[requires(stack(stack))]
#[ensures(result >= 0)]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    #[ensures(stack_owned(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(stack))]
    #[ensures(result == (*stack).head.is_null())]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        result
    }

    #[requires(stack(stack))]
    #[ensures(result >= 0)]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }

    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack) && !(*stack).head.is_null())]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack_owned(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        let mut n = (*stack).head;
        #[invariant(node_owned(n))]
        loop {
            if n.is_null() {
                break;
            }

            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }

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