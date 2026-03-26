use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(*mut Node n; i32 value, *mut Node next) =
    n != null_mut() &*&
    [1/2]n as *mut u8 |-> _ &*&
    struct_Node_padding(n) &*&
    (*n).value |-> value &*&
    (*n).next |-> next;

predicate node_list(*mut Node n; list<i32> values) =
    match values {
        cons(h, t) => node(n, h, ?next) &*& node_list(next, t),
        nil => n == null_mut(),
    };

predicate stack(*mut Stack s; list<i32> values) =
    s != null_mut() &*&
    [1/2]s as *mut u8 |-> _ &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> ?head &*&
    node_list(head, values);

unsafe fn dispose_nodes(n: *mut Node)
    requires node_list(n, ?values);
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
        ensures stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        return stack;
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
        requires stack(stack, ?values);
        ensures stack(stack, values) &*& result == (values == nil);
    {
        let head = (*stack).head;
        let result = head.is_null();
        return result;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack(stack, ?values);
        ensures stack(stack, cons(value, values));
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
        requires stack(stack, cons(?head_value, ?tail_values));
        ensures stack(stack, tail_values) &*& result == head_value;
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        return result;
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack(stack, ?values);
        ensures true;
    {
        dispose_nodes((*stack).head);
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