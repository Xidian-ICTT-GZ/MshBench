use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

predicate node_list(*mut Node n, Vec<i32> values) =
    match values {
        [] => n == null_mut(),
        [head_val] + tail_vals => n != null_mut() && *n |-> Node { next: ?next_ptr, value: head_val } * node_list(next_ptr, tail_vals)
    };

predicate stack_pred(*mut Stack s, Vec<i32> values) =
    s != null_mut() && *s |-> Stack { head: ?h } * node_list(h, values);

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
    requires
        forall|i: i32| #[trigger] p(i) == (i != 20),
        node_list(n, ?old_values),
    ensures
        node_list(result, filter_vec(old_values, p)),
{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        let keep = p((*n).value);
        let next;
        if keep {
            let old_next = (*n).next;
            next = filter_nodes(old_next, p);
            (*n).next = next;
            n
        } else {
            next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    requires
        node_list(n, _),
    ensures
        true,
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        requires
            true,
        ensures
            stack_pred(result, vec![]),
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires
            stack_pred(stack, ?old_values),
        ensures
            stack_pred(stack, cons(value, old_values)),
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
        requires
            stack_pred(stack, ?old_values),
            old_values.len() > 0,
        ensures
            stack_pred(stack, tail(old_values)),
            result == head(old_values),
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
        requires
            stack_pred(stack, ?old_values),
            forall|i: i32| #[trigger] p(i) == (i != 20),
        ensures
            stack_pred(stack, filter_vec(old_values, p)),
    {
        let head = filter_nodes((*stack).head, p);
        (*stack).head = head;
    }

    unsafe fn dispose(stack: *mut Stack)
        requires
            stack_pred(stack, _),
        ensures
            true,
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool {
    x != 20
}

lemma void cons_lemma<T>(x: T, xs: Vec<T>)
    ensures
        cons(x, xs) == [x] + xs,
{
}

lemma void head_lemma(xs: Vec<i32>)
    requires
        xs.len() > 0,
    ensures
        head(xs) == xs[0],
{
}

lemma void tail_lemma(xs: Vec<i32>)
    requires
        xs.len() > 0,
    ensures
        tail(xs) == xs[1..].to_vec(),
{
}

pure fn cons<T>(x: T, xs: Vec<T>) -> Vec<T>
{
    [x] + xs
}

pure fn head(xs: Vec<i32>) -> i32
{
    xs[0]
}

pure fn tail(xs: Vec<i32>) -> Vec<i32>
{
    xs[1..].to_vec()
}

pure fn filter_vec(xs: Vec<i32>, p: fn(i32) -> bool) -> Vec<i32>
{
    let mut r = Vec::new();
    let mut i = 0;
    while i < xs.len()
        invariant
            r == filter_vec_prefix(xs, p, i),
            0 <= i && i <= xs.len(),
    {
        if p(xs[i]) {
            r.push(xs[i]);
        }
        i += 1;
    }
    r
}

pure fn filter_vec_prefix(xs: Vec<i32>, p: fn(i32) -> bool, n: int) -> Vec<i32>
{
    if n <= 0 {
        vec![]
    } else {
        let prefix = filter_vec_prefix(xs, p, n - 1);
        if p(xs[(n - 1) as usize]) {
            prefix + [xs[(n - 1) as usize]]
        } else {
            prefix
        }
    }
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