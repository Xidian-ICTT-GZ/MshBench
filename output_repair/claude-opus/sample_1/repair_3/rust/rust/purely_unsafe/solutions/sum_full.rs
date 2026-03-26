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
    (node == std::ptr::null_mut() && len == 0) ||
    (node != std::ptr::null_mut() && len > 0 && malloc_block_node(node) && node_list((*node).next, len - 1));

pred stack_inv(stack: *mut Stack) =
    malloc_block_Stack(stack) && node_list((*stack).head, 0) || 
    malloc_block_Stack(stack) && node_list((*stack).head, 1) ||
    malloc_block_Stack(stack) && node_list((*stack).head, 2) ||
    malloc_block_Stack(stack) && node_list((*stack).head, 3);
@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    //@ requires node == std::ptr::null_mut() || malloc_block_node(node);
    //@ ensures true;
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    //@ requires true;
    //@ ensures stack_inv(result);
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    //@ requires stack_inv(stack);
    //@ ensures true;
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }

    //@ requires stack_inv(stack);
    //@ ensures stack_inv(stack);
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    //@ requires stack_inv(stack) && (*stack).head != std::ptr::null_mut();
    //@ ensures stack_inv(stack);
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    //@ requires stack_inv(stack);
    //@ ensures true;
    unsafe fn dispose(stack: *mut Stack) {
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