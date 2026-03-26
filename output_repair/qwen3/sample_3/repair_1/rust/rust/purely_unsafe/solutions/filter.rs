use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

#[predicate]
fn node_list(n: *mut Node, values: Vec<i32>) -> bool {
    match values.as_slice() {
        [] => n.is_null(),
        [head_val, tail @ ..] => !n.is_null() && (*n).value == *head_val && node_list((*n).next, tail.to_vec()),
    }
}

#[predicate]
fn stack_pred(s: *mut Stack, values: Vec<i32>) -> bool {
    !s.is_null() && stack_fields(s, values)
}

#[predicate]
fn stack_fields(s: *mut Stack, values: Vec<i32>) -> bool {
    node_list((*s).head, values)
}

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node {
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);

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

unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(true)]
    #[ensures(stack_pred(result, vec![]))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack_pred(stack, old_values))]
    #[ensures(stack_pred(stack, cons(value, old_values)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_pred(stack, old_values) && old_values.len() > 0)]
    #[ensures(stack_pred(stack, tail(old_values)) && result == head(old_values))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack_pred(stack, old_values))]
    #[ensures(stack_pred(stack, filter_vec(old_values, p)))]
    unsafe fn filter(stack: *mut Stack, p: I32Predicate) {
        let head = filter_nodes((*stack).head, p);

        (*stack).head = head;
    }

    #[requires(stack_pred(stack, _))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool {
    x != 20
}

#[trusted]
#[logic]
fn cons<T>(x: T, xs: Vec<T>) -> Vec<T> {
    let mut r = xs;
    r.insert(0, x);
    r
}

#[trusted]
#[logic]
fn head<T>(xs: Vec<T>) -> T {
    xs[0]
}

#[trusted]
#[logic]
fn tail<T>(xs: Vec<T>) -> Vec<T> {
    xs[1..].to_vec()
}

#[trusted]
#[logic]
fn filter_vec(xs: Vec<i32>, p: I32Predicate) -> Vec<i32> {
    let mut r = Vec::new();
    for x in xs {
        if p(x) {
            r.push(x);
        }
    }
    r
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