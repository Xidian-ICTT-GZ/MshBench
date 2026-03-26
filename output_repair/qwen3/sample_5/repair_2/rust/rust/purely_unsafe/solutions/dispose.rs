use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(*mut Node n; i32 value, *mut Node next) = 
    n |-> struct Node { next: next, value: value };

predicate node_list(*mut Node n) =
    n == std::ptr::null_mut() ?
        true
    :
        exists(i32 v, *mut Node next). node(n, v, next) && node_list(next);

predicate stack(*mut Stack s) =
    s != std::ptr::null_mut() &&
    exists(*mut Node h). s |-> struct Stack { head: h } && node_list(h);

unsafe fn dispose_nodes(n: *mut Node)
    requires node_list(n);
    ensures true;
{
    if !n.is_null() {
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        requires true;
        ensures stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        leak stack |-> struct Stack { head: std::ptr::null_mut() };
        return stack;
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
        requires stack(stack);
        ensures stack(stack) && result == ((*stack).head == std::ptr::null_mut());
    {
        let result = (*stack).head.is_null();
        return result;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack(stack);
        ensures stack(stack);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        leak node(n, value, (*n).next);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack(stack) && (*stack).head != std::ptr::null_mut();
        ensures stack(stack);
    {
        let head = (*stack).head;
        let result = (*head).value;
        let next = (*head).next;
        (*stack).head = next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        return result;
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack(stack);
        ensures true;
    {
        let head = (*stack).head;
        dispose_nodes(head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
    requires true;
    ensures true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}