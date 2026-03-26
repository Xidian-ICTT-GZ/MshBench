use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

predicate node(*mut Node n; i32 v, *mut Node next_) =
    n != null_mut() &*&
    (*n).value |-> v &*&
    (*n).next |-> next_;

predicate nodes(*mut Node n; list<i32> vs) =
    n == null_mut() && vs == []
    ||
    exists(i32 v, *mut Node next_ ::
        node(n, v, next_) &*&
        nodes(next_, ?tail) &*&
        vs == cons(v, tail));

predicate stack(*mut Stack s; list<i32> vs) =
    s != null_mut() &*&
    (*s).head |-> ?head &*&
    nodes(head, vs);

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    requires *n |-> ?head &*& nodes(head, ?vs);
    ensures *n |-> ?head2 &*& nodes(head2, ?vs2) &*&
            foreach(vs2, (fun(x: i32) => p(x))) &*&
            foreach(vs, (fun(x: i32) => mem(x, vs2) || !p(x)));
{
    if !(*n).is_null() {
        let current = *n;
        open nodes(current, _);
        let v = (*current).value;
        let keep = p(v);
        if keep {
            let next_ptr = &raw mut (*current).next;
            close node(current, v, *next_ptr);
            filter_nodes(next_ptr, p);
            open nodes(?next_val, ?tail_vs);
            close nodes(current, cons(v, tail_vs));
        } else {
            let next_ = (*current).next;
            close node(current, v, next_);
            dealloc(current as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
            // vs2 is the filtered tail; since v was removed, vs = cons(v, tail) and vs2 = filtered(tail)
        }
    } else {
        close nodes(null_mut(), []);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    requires nodes(n, ?vs);
    ensures emp;
{
    if !n.is_null() {
        open nodes(n, _);
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    } else {
        close nodes(null_mut(), []);
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        requires emp;
        ensures stack(result, []);
    {
        let layout = Layout::new::<Stack>();
        let stack = alloc(layout) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(layout);
        }
        (*stack).head = std::ptr::null_mut();
        close stack(stack, []);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack(stack, ?vs);
        ensures stack(stack, cons(value, vs));
    {
        open stack(stack, vs);
        let layout = Layout::new::<Node>();
        let n = alloc(layout) as *mut Node;
        if n.is_null() {
            handle_alloc_error(layout);
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        close node(n, value, (*stack).head);
        close nodes(n, cons(value, vs));
        close stack(stack, cons(value, vs));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack(stack, ?vs) &*& vs != [];
        ensures stack(stack, ?vs2) &*& result == head(vs) &*& vs2 == tail(vs);
    {
        open stack(stack, vs);
        let head = (*stack).head;
        open nodes(head, vs);
        let result = (*head).value;
        let next = (*head).next;
        (*stack).head = next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        close nodes(next, tail(vs));
        close stack(stack, tail(vs));
        result
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
        requires stack(stack, ?vs);
        ensures stack(stack, ?vs2) &*&
                foreach(vs2, (fun(x: i32) => p(x))) &*&
                foreach(vs, (fun(x: i32) => mem(x, vs2) || !p(x)));
    {
        open stack(stack, vs);
        let head_ptr = &raw mut (*stack).head;
        filter_nodes(head_ptr, p);
        close stack(stack, _);
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack(stack, ?vs);
        ensures emp;
    {
        open stack(stack, vs);
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