use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(*mut Node) = 
    match result {
        null => true,
        _ => exists(next: *mut Node, value: i32). sep!(
            node(result, next, value),
            node_list(next)
        )
    };

predicate node(*mut Node, *mut Node, i32) = 
    *result |-> Node { next: arg1, value: arg2 };

predicate stack_inv(*mut Stack) = 
    exists(head: *mut Node). sep!(
        *result |-> Stack { head },
        node_list(head)
    );

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    requires node_list(nodes),
    ensures node_list(nodes)
{
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    unsafe fn create() -> *mut Stack
        requires true,
        ensures stack_inv(result)
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
        requires stack_inv(stack),
        ensures stack_inv(stack)
    {
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        result
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires stack_inv(stack),
        ensures stack_inv(stack)
    {
        let result = get_nodes_sum((*stack).head);

        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack_inv(stack),
        ensures stack_inv(stack)
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
        requires stack_inv(stack), (*stack).head != null,
        ensures stack_inv(stack)
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack_inv(stack),
        ensures true
    {
        let mut n = (*stack).head;
        loop
            invariant exists(h: *mut Node). sep!(
                *stack |-> Stack { head: h },
                node_list(h),
                node_list(n)
            ),
            n == h || n != null ==> node_list(n)
        {
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