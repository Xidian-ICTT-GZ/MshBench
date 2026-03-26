use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_pred(node: *mut Node, next: *mut Node, value: i32) =
    node |-> Node { next: next, value: value };

#[predicate]
fn stack_pred(stack: *mut Stack, head: *mut Node) =
    stack |-> Stack { head: head };

#[predicate]
fn list_seg(start: *mut Node, end: *mut Node) =
    start == end ?
        emp
    :
        start |-> Node { next: ?next, value: ?val } &*&
        node_pred(start, next, val) &*&
        list_seg(next, end);

#[predicate]
fn list_sum(node: *mut Node, sum: int) =
    node == std::ptr::null_mut() ?
        emp &*& sum == 0
    :
        node |-> Node { next: ?next, value: ?val } &*&
        node_pred(node, next, val) &*&
        list_sum(next, ?tail_sum) &*&
        sum == val + tail_sum;

#[predicate]
fn stack_list(stack: *mut Stack, head: *mut Node) =
    stack |-> Stack { head: head };

unsafe fn get_nodes_sum(node: *mut Node) -> i32
    requires node == std::ptr::null_mut() || (node |-> Node { next: ?next, value: ?val } &*& list_sum(next, ?tail_sum));
    ensures list_sum(node, result);
{
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }
    result
}

impl Stack {
    unsafe fn create() -> *mut Stack
        requires true;
        ensures result != std::ptr::null_mut() &*& stack_pred(result, std::ptr::null_mut());
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires stack_pred(stack, ?head) &*& list_sum(head, ?l_sum);
        ensures stack_pred(stack, head) &*& list_sum(head, result);
    {
        let result = get_nodes_sum((*stack).head);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack_pred(stack, ?old_head) &*& list_seg(std::ptr::null_mut(), old_head);
        ensures stack_pred(stack, ?new_head) &*& list_seg(std::ptr::null_mut(), new_head);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack_pred(stack, ?head) &*& head != std::ptr::null_mut() &*& head |-> Node { next: ?next, value: ?val };
        ensures stack_pred(stack, next) &*& result == val;
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack_pred(stack, ?head) &*& list_seg(head, std::ptr::null_mut());
        ensures emp;
    {
        let mut current = (*stack).head;
        while current != std::ptr::null_mut()
            invariant stack_pred(stack, (*stack).head) &*& list_seg(current, std::ptr::null_mut());
        {
            let next = (*current).next;
            dealloc(current as *mut u8, Layout::new::<Node>());
            current = next;
        }
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