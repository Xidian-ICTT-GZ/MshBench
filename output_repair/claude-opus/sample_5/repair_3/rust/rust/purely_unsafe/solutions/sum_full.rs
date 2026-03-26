use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred node_list(node: *mut Node, len: i32) =
    if node.is_null() {
        len == 0
    } else {
        len > 0 &&
        malloc_block_node(node) &&
        node_list((*node).next, len - 1)
    };

pred stack_inv(stack: *mut Stack, len: i32) =
    malloc_block_Stack(stack) &&
    len >= 0 &&
    node_list((*stack).head, len);
@*/

/*@
fn create_stack_spec() -> *mut Stack
    requires true
    ensures stack_inv(result, 0)
@*/
unsafe fn create_stack() -> *mut Stack {
    let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
    if stack.is_null() {
        handle_alloc_error(Layout::new::<Stack>());
    }
    (*stack).head = std::ptr::null_mut();
    stack
}

/*@
fn get_nodes_sum_spec(node: *mut Node, len: i32) -> i32
    requires node.is_null() ? len == 0 : (len > 0 && malloc_block_node(node) && node_list((*node).next, len - 1))
    ensures true
@*/
unsafe fn get_nodes_sum(node: *mut Node, len: i32) -> i32 {
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next, len - 1);
        result = (*node).value + tail_sum;
    }
    result
}

/*@
fn stack_get_sum_spec(stack: *mut Stack, len: i32) -> i32
    requires stack_inv(stack, len)
    ensures stack_inv(stack, len)
@*/
unsafe fn stack_get_sum(stack: *mut Stack, len: i32) -> i32 {
    let result = get_nodes_sum((*stack).head, len);
    result
}

/*@
fn stack_push_spec(stack: *mut Stack, value: i32, len: i32)
    requires stack_inv(stack, len) && len >= 0
    ensures stack_inv(stack, len + 1)
@*/
unsafe fn stack_push(stack: *mut Stack, value: i32, len: i32) {
    let n = alloc(Layout::new::<Node>()) as *mut Node;
    if n.is_null() {
        handle_alloc_error(Layout::new::<Node>());
    }
    (*n).next = (*stack).head;
    (*n).value = value;
    (*stack).head = n;
}

/*@
fn stack_pop_spec(stack: *mut Stack, len: i32) -> i32
    requires stack_inv(stack, len) && len > 0
    ensures stack_inv(stack, len - 1)
@*/
unsafe fn stack_pop(stack: *mut Stack, len: i32) -> i32 {
    let head = (*stack).head;
    let result = (*head).value;
    (*stack).head = (*head).next;
    dealloc(head as *mut u8, Layout::new::<Node>());
    result
}

/*@
fn stack_dispose_spec(stack: *mut Stack, len: i32)
    requires stack_inv(stack, len) && len == 0
    ensures true
@*/
unsafe fn stack_dispose(stack: *mut Stack, len: i32) {
    dealloc(stack as *mut u8, Layout::new::<Stack>());
}

fn main() {
    unsafe {
        let s = create_stack();
        stack_push(s, 10, 0);
        stack_push(s, 20, 1);
        let _sum = stack_get_sum(s, 2);

        let _result1 = stack_pop(s, 2);

        let _result2 = stack_pop(s, 1);

        stack_dispose(s, 0);
    }
}