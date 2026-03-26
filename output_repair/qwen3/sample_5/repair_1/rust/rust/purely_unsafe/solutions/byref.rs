use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

predicate nodes(*mut Node n; list<i32> vs) =
    n == null_mut() && vs == []
    || n != null_mut() && exists(i32 v, *mut Node next_ :: 
        (*n).value |-> v &*& (*n).next |-> next_ &*& nodes(next_, ?tail) &*& vs == cons(v, tail));

predicate stack(*mut Stack s; list<i32> vs) =
    s != null_mut() &*& (*s).head |-> ?head &*& nodes(head, vs);

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    requires *n |-> ?head &*& nodes(head, ?vs) &*& foreach(vs, (fun(x: i32) => true));
    ensures *n |-> ?head2 &*& nodes(head2, ?vs2) &*& foreach(vs2, (fun(x: i32) => p(x))) &*& 
            foreach(vs, (fun(x: i32) => mem(x, vs2) || !p(x)));
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
        ensures stack(stack, cons(value, vs));
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
        requires stack(stack, ?vs) &*& vs != [];
        ensures stack(stack, ?vs2) &*& result == head(vs) &*& vs2 == tail(vs);
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
        requires stack(stack, ?vs);
        ensures stack(stack, ?vs2) &*& foreach(vs2, (fun(x: i32) => p(x))) &*& 
                foreach(vs, (fun(x: i32) => mem(x, vs2) || !p(x)));
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

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}