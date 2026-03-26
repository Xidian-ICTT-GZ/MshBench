use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn nodes(node: *mut Node) -> bool {
    if node.is_null() {
        true
    } else {
        alloc::points_to(node, Node { next: (*node).next, value: (*node).value }) 
        &*& nodes((*node).next)
    }
}

#[predicate]
fn stack(stack: *mut Stack) -> bool {
    alloc::points_to(stack, Stack { head: (*stack).head }) &*& nodes((*stack).head)
}

#[requires(stack@stack)]
#[ensures(stack@stack)]
unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    let mut result = 0;
    if !node.is_null() {
        #[invariant(nodes(node))]
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }
    result
}

impl Stack {
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    #[requires(stack(stack))]
    #[ensures(stack(stack))]
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
    
    #[requires(stack(stack) &*& (*stack).head != std::ptr::null_mut())]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(stack(stack))]
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
        let sum = Stack::get_sum(s);
        let result1 = Stack::pop(s);
        let result2 = Stack::pop(s);
        Stack::dispose(s);
    }
}