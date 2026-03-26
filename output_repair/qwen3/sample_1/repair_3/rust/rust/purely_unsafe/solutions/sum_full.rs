use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(node: *mut Node; len: int) =
    if node == null() {
        len == 0
    } else {
        len > 0 &&
        malloc_block_Node(node) &&
        node_list((*node).next, len - 1)
    };

predicate stack_inv(stack: *mut Stack) =
    malloc_block_Stack(stack) &&
    exists(len: int, node_list((*stack).head, len));

#[requires(true)]
#[ensures(stack_inv(result))]
unsafe fn create_stack() -> *mut Stack {
    let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
    if stack.is_null() {
        handle_alloc_error(Layout::new::<Stack>());
    }
    (*stack).head = null();
    stack
}

#[requires(node == null() || (exists(len: int, node_list(node, len))))]
#[ensures(is_positive(result))]
unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    let mut result = 0;
    if node != null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }
    result
}

#[requires(stack_inv(stack))]
#[ensures(is_positive(result))]
unsafe fn stack_get_sum(stack: *mut Stack) -> i32 {
    let result = get_nodes_sum((*stack).head);
    result
}

#[requires(stack_inv(stack))]
#[ensures(stack_inv(stack))]
unsafe fn stack_push(stack: *mut Stack, value: i32) {
    let n = alloc(Layout::new::<Node>()) as *mut Node;
    if n.is_null() {
        handle_alloc_error(Layout::new::<Node>());
    }
    (*n).next = (*stack).head;
    (*n).value = value;
    (*stack).head = n;
}

#[requires(stack_inv(stack) && (*stack).head != null())]
#[ensures(stack_inv(stack))]
unsafe fn stack_pop(stack: *mut Stack) -> i32 {
    let head = (*stack).head;
    let result = (*head).value;
    (*stack).head = (*head).next;
    dealloc(head as *mut u8, Layout::new::<Node>());
    result
}

#[requires(stack_inv(stack))]
#[ensures(true)]
unsafe fn stack_dispose(stack: *mut Stack) {
    dealloc(stack as *mut u8, Layout::new::<Stack>());
}

fn main() {
    unsafe {
        let s = create_stack();
        stack_push(s, 10);
        stack_push(s, 20);
        let sum = stack_get_sum(s);

        let result1 = stack_pop(s);

        let result2 = stack_pop(s);

        stack_dispose(s);
    }
}