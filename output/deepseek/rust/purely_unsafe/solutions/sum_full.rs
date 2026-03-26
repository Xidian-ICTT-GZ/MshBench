use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn nodes_sum(node: *mut Node, sum: i32) -> bool {
    if node.is_null() {
        sum == 0
    } else {
        exists!(
            tail_sum: i32,
            nodes_sum((*node).next, tail_sum) && sum == (*node).value + tail_sum
        )
    }
}

#[predicate]
fn node_own(node: *mut Node) -> bool {
    !node.is_null() && exists!(
        next: *mut Node,
        value: i32,
        (*node).next == next && (*node).value == value
    )
}

#[predicate]
fn nodes(node: *mut Node) -> bool {
    if node.is_null() {
        true
    } else {
        node_own(node) && nodes((*node).next)
    }
}

#[predicate]
fn stack_own(stack: *mut Stack) -> bool {
    !stack.is_null() && exists!(head: *mut Node, (*stack).head == head)
}

#[predicate]
fn stack(stack: *mut Stack) -> bool {
    stack_own(stack) && nodes((*stack).head)
}

unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    #[requires(nodes(node))]
    #[ensures(nodes(node) && nodes_sum(node, result))]
    let mut result = 0;
    if !node.is_null() {
        #[invariant(nodes(node))]
        #[invariant(nodes_sum(node, result))]
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    unsafe fn create() -> *mut Stack {
        #[ensures(stack(result))]
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        #[requires(stack(stack))]
        #[ensures(stack(stack) && nodes_sum((*stack).head, result))]
        let result = get_nodes_sum((*stack).head);

        result
    }

    unsafe fn push(stack: *mut Stack, value: i32) {
        #[requires(stack(stack))]
        #[ensures(stack(stack))]
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32 {
        #[requires(stack(stack) && !(*stack).head.is_null())]
        #[ensures(stack(stack))]
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack) {
        #[requires(stack(stack))]
        #[ensures(true)]
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let sum = Stack::get_sum(s);

        let result1 = Stack::pop(s);

        let result2 = Stack::pop(s);

        Stack::dispose(s);
    }
}