use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(*mut Node n; i32 value, *mut Node next) =
    n != std::ptr::null_mut() &*&
    [1/2]n as *mut u8 |-> _ &*&
    struct_Node_padding(n) &*&
    [1/2]n.next |-> next &*&
    [1/2]n.value |-> value;

predicate nodes(*mut Node n) =
    n == std::ptr::null_mut() ? true :
    exists(?value, ?next) &*& node(n, value, next) &*& nodes(next);

predicate stack(*mut Stack s) =
    s != std::ptr::null_mut() &*&
    [1/2]s as *mut u8 |-> _ &*&
    struct_Stack_padding(s) &*&
    [1/2]s.head |-> ?head &*&
    nodes(head);

lemma void nodes_split(*mut Node n)
    requires nodes(n);
    ensures nodes(n);
{
    if n != std::ptr::null_mut() {
        open nodes(n);
        let value = *(&(*n).value);
        let next = *(&(*n).next);
        close node(n, value, next);
        nodes_split(next);
        close nodes(n);
    }
}

lemma void nodes_merge(*mut Node n)
    requires nodes(n);
    ensures nodes(n);
{
    if n != std::ptr::null_mut() {
        open nodes(n);
        let value = *(&(*n).value);
        let next = *(&(*n).next);
        close node(n, value, next);
        nodes_merge(next);
        close nodes(n);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    requires nodes(n);
    ensures emp;
{
    if n != std::ptr::null_mut() {
        open nodes(n);
        let next = (*n).next;
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
        ensures stack(stack) &*& result == ((*stack).head == std::ptr::null_mut());
    {
        let result = (*stack).head.is_null();
        return result;
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
        close nodes(n);
        close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack(stack) &*& (*stack).head != std::ptr::null_mut();
        ensures stack(stack);
    {
        open stack(stack);
        let head = (*stack).head;
        open nodes(head);
        let value = (*head).value;
        let next = (*head).next;
        (*stack).head = next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        close nodes(next);
        close stack(stack);
        return value;
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