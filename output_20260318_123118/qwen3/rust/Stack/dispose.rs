use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate node(*mut Node n; i32 value, *mut Node next) =
    n |-> struct Node { next: next, value: value };

predicate stack(*mut Stack s; list<*mut Node> nodes) =
    s |-> struct Stack { head: ?head } &*&
    stack_nodes(head, nodes);

predicate stack_nodes(*mut Node head; list<*mut Node> nodes) =
    match nodes {
        cons(n, rest) => node(n, ?v, ?next) &*& stack_nodes(next, rest),
        nil => head == std::ptr::null_mut()
    };

unsafe fn dispose_nodes(n: *mut Node)
    requires stack_nodes(n, ?nodes);
    ensures emp;
{
    if !n.is_null() {
        open stack_nodes(n, _);
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
        requires emp;
        ensures stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close stack(stack, nil);
        return stack;
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
        requires stack(stack, ?nodes);
        ensures stack(stack, nodes) &*& result == (nodes == nil);
    {
        open stack(stack, nodes);
        let head = (*stack).head;
        close stack(stack, nodes);
        let result = head.is_null();
        return result;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack(stack, ?nodes);
        ensures stack(stack, cons(?n, nodes));
    {
        open stack(stack, nodes);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        close node(n, value, (*stack).head);
        close stack(stack, cons(n, nodes));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack(stack, cons(?n, ?rest));
        ensures stack(stack, rest) &*& result == ?v &*& node(n, v, ?next);
    {
        open stack(stack, cons(n, rest));
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        close stack(stack, rest);
        return result;
    }
    
    unsafe fn dispose(stack: *mut Stack)
        requires stack(stack, ?nodes);
        ensures emp;
    {
        open stack(stack, nodes);
        dispose_nodes((*stack).head);
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