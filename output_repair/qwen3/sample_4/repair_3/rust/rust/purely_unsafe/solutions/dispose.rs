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
    n == null_mut::<Node>() ||
    exists(i32 v, *mut Node next). node(n, v, next) && node_list(next);

predicate stack_inv(*mut Stack s) =
    s |-> struct Stack { head: ?head } && node_list(head);

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
        ensures stack_inv(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        leak stack |-> struct Stack { head: null_mut::<Node>() };
        return stack;
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
        requires stack_inv(stack);
        ensures stack_inv(stack) && result == ((*stack).head == null_mut::<Node>());
    {
        let head = (*stack).head;
        let result = head.is_null();
        return result;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack_inv(stack);
        ensures stack_inv(stack);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        close node(n, value, (*n).next);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack_inv(stack) && (*stack).head != null_mut::<Node>();
        ensures stack_inv(stack);
    {
        let head = (*stack).head;
        open node(head, ?v, ?next);
        let result = v;
        (*stack).head = next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        return result;
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack_inv(stack);
        ensures true;
    {
        let head = (*stack).head;
        open stack_inv(stack);
        dispose_nodes(head);
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