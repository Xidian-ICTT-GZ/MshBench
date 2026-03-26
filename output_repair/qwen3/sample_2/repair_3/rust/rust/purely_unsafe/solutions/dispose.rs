use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(*mut Node n; i32 value, *mut Node next) = 
    n as *mut u8 |-> _ &*& 
    (*n).value |-> value &*& 
    (*n).next |-> next;

predicate node_list(*mut Node n) =
    n == std::ptr::null_mut() ?
        emp
    :
        node(n, ?v, ?next) &*& node_list(next);

predicate stack(*mut Stack s) = 
    s as *mut u8 |-> _ &*& 
    (*s).head |-> ?h &*& node_list(h);

unsafe fn dispose_nodes(n: *mut Node)
    requires node_list(n),
    ensures emp;
{
    if !n.is_null() {
        let next = (*n).next;
        open node_list(n);
        open node(n, _, next);
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        requires emp,
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
        requires stack(stack),
        ensures stack(stack);
    {
        open stack(stack);
        let h = (*stack).head;
        let result = h.is_null();
        close stack(stack);
        return result;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack(stack),
        ensures stack(stack);
    {
        open stack(stack);
        let layout = Layout::new::<Node>();
        let n = alloc(layout) as *mut Node;
        if n.is_null() {
            handle_alloc_error(layout);
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack(stack) &*& (*stack).head != std::ptr::null_mut(),
        ensures stack(stack);
    {
        open stack(stack);
        let head = (*stack).head;
        open node_list(head);
        open node(head, ?v, ?next);
        let result = v;
        (*stack).head = next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        close node_list(next);
        close stack(stack);
        return result;
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack(stack),
        ensures emp;
    {
        open stack(stack);
        let h = (*stack).head;
        dispose_nodes(h);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
    requires emp,
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