use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

predicate node(*mut Node n; i32 value, *mut Node next) =
    n != null && [_]std::ptr::read(n) |-> struct Node { next: next, value: value };

predicate nodes(*mut Node head; list<i32> values) =
    match values {
        [] => head == null,
        ?v :: ?vs => exists(?n) node(head, v, n) * nodes(n, vs)
    };

predicate stack(*mut Stack s; list<i32> values) =
    s != null && [_]std::ptr::read(s) |-> struct Stack { head: ?head } * nodes(head, values);

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    requires *n |-> ?head * nodes(head, ?vs) * foreach(vs, (|v: i32| sep(pure(p(v) || true))));
    ensures *n |-> ?new_head * nodes(new_head, ?filtered_vs) * foreach(filtered_vs, (|v: i32| sep(pure(p(v)))));
{
    if !(*n).is_null() {
        let keep = p((**n).value);
        if keep {
            filter_nodes(&raw mut (**n).next, p);
        } else {
            let next_ = (**n).next;
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    requires nodes(n, ?vs);
    ensures emp;
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        requires emp;
        ensures stack(result, []);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack(stack, ?vs);
        ensures stack(stack, [value] + vs);
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
        requires stack(stack, ?v :: ?vs);
        ensures stack(stack, vs) &*& result == v;
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
        requires stack(stack, ?vs) * foreach(vs, (|v: i32| sep(pure(p(v) || true))));
        ensures stack(stack, ?filtered_vs) * foreach(filtered_vs, (|v: i32| sep(pure(p(v)))));
    {
        filter_nodes(&raw mut (*stack).head, p);
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack(stack, ?vs);
        ensures emp;
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool {
    x != 20
}

fn main()
    requires emp;
    ensures emp;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}