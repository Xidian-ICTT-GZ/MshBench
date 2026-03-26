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
    if n == std::ptr::null_mut() then
        true
    else
        exists(i32 v, *mut Node next). node(n, v, next) * node_list(next);

predicate stack(*mut Stack s) =
    s != std::ptr::null_mut() &&
    exists(*mut Node h). s |-> struct Stack { head: h } * node_list(h);

unsafe fn dispose_nodes(n: *mut Node)
    requires node_list(n);
    ensures emp;
{
    if !n.is_null() {
        let next = (*n).next;
        open node_list(n);
        assert(node(n, _, next));
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        requires emp;
        ensures stack(result);
    {
        let layout = Layout::new::<Stack>();
        let stack = alloc(layout) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(layout);
        }
        (*stack).head = std::ptr::null_mut();
        close stack(stack);
        return stack;
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
        requires stack(stack);
        ensures stack(stack) && result == ((*stack).head == std::ptr::null_mut());
    {
        open stack(stack);
        let h = (*stack).head;
        close stack(stack);
        return h.is_null();
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack(stack);
        ensures stack(stack);
    {
        open stack(stack);
        let old_head = (*stack).head;
        let layout = Layout::new::<Node>();
        let n = alloc(layout) as *mut Node;
        if n.is_null() {
            handle_alloc_error(layout);
        }
        (*n).next = old_head;
        (*n).value = value;
        (*stack).head = n;
        close node(n, value, old_head);
        close node_list(n);
        close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack(stack) && (*stack).head != std::ptr::null_mut();
        ensures stack(stack);
    {
        open stack(stack);
        let head = (*stack).head;
        open node_list(head);
        assert(node(head, _, _));
        let result = (*head).value;
        let next = (*head).next;
        (*stack).head = next;
        close node_list(next);
        close stack(stack);
        dealloc(head as *mut u8, Layout::new::<Node>());
        return result;
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack(stack);
        ensures emp;
    {
        open stack(stack);
        let head = (*stack).head;
        dispose_nodes(head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
    requires emp;
    ensures emp;
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