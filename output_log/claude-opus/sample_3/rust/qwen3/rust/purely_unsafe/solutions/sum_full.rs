use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_pred(node: *mut Node, next: *mut Node, value: i32) =
    node |-> Node { next: next, value: value };

#[predicate]
fn nodes_list(node: *mut Node, sum: int) =
    node == std::ptr::null_mut()
    ? emp &*& sum == 0
    : node_pred(node, ?next, ?v) &*& nodes_list(next, ?tail_sum) &*& sum == v + tail_sum;

#[predicate]
fn stack_pred(stack: *mut Stack, head: *mut Node) =
    stack |-> Stack { head: head };

#[predicate]
fn stack_list(stack: *mut Stack, head: *mut Node, sum: int) =
    stack_pred(stack, head) &*& nodes_list(head, sum);

unsafe fn get_nodes_sum(node: *mut Node) -> i32
    #[requires(node == std::ptr::null_mut() ? emp : node_pred(node, ?next, ?val) &*& nodes_list(next, ?tail_sum))]
    #[ensures(nodes_list(node, result))]
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
        #[requires(emp)]
        #[ensures(stack_list(result, std::ptr::null_mut(), 0))]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
        #[requires(stack_list(stack, ?head, ?sum))]
        #[ensures(stack_list(stack, head, sum) &*& result == sum)]
    {
        let result = get_nodes_sum((*stack).head);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires(stack_list(stack, ?old_head, ?old_sum))]
        #[ensures(stack_list(stack, result, old_sum + value) &*& node_pred(result, old_head, value))]
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
        #[requires(stack_list(stack, ?head, ?sum) &*& head != std::ptr::null_mut() &*&
                   node_pred(head, ?next, ?val) &*& nodes_list(next, ?tail_sum) &*& sum == val + tail_sum)]
        #[ensures(stack_list(stack, next, tail_sum) &*& result == val)]
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack)
        #[requires(stack_list(stack, ?head, ?sum))]
        #[ensures(emp)]
    {
        let mut curr = (*stack).head;
        while (curr != std::ptr::null_mut())
            invariant(nodes_list(curr, ?remaining_sum))
        {
            let next = (*curr).next;
            dealloc(curr as *mut u8, Layout::new::<Node>());
            curr = next;
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