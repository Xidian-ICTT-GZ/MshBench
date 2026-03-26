use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

#[verifast::predicate]
pub fn node_list(n: *mut Node, values: Vec<i32>) -> bool {
    match values.as_slice() {
        [] => n == std::ptr::null_mut(),
        [head_val, tail @ ..] => {
            verifast::std::pointer::points_to(n, Node { next: (*n).next, value: *head_val }) &&
            node_list((*n).next, tail.to_vec())
        }
    }
}

#[verifast::predicate]
pub fn stack_pred(s: *mut Stack, values: Vec<i32>) -> bool {
    verifast::std::pointer::points_to(s, Stack { head: (*s).head }) &&
    node_list((*s).head, values)
}

#[requires(match n { std::ptr::null_mut() => true, _ => exists(values: Vec<i32>, node_list(n, values)) })]
#[ensures(exists(result_values: Vec<i32>, node_list(result, result_values) && forall(i: usize, i < result_values.len() ==> p(result_values[i])) && (match old(n) { std::ptr::null_mut() => result_values == vec![], _ => exists(old_values: Vec<i32>, node_list(old(n), old_values) && forall(i: usize, i < old_values.len() ==> (!p(old_values[i]) || exists(j: usize, j < result_values.len() && result_values[j] == old_values[i])))) }))]
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

#[requires(match n { std::ptr::null_mut() => true, _ => exists(values: Vec<i32>, node_list(n, values)) })]
#[ensures(true)]
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

    #[requires(stack_pred(stack, ?old_values))]
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

    #[requires(stack_pred(stack, ?old_values) &*& old_values.len() > 0)]
    #[ensures(stack_pred(stack, tail(old_values)) &*& result == head(old_values))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack_pred(stack, ?old_values))]
    #[ensures(stack_pred(stack, ?new_values) &*& forall(i: usize, i < new_values.len() ==> p(new_values[i])) &*& forall(i: usize, i < old_values.len() ==> (!p(old_values[i]) || exists(j: usize, j < new_values.len() && new_values[j] == old_values[i])))]
    unsafe fn filter(stack: *mut Stack, p: I32Predicate) {
        let head = filter_nodes((*stack).head, p);

        (*stack).head = head;
    }

    #[requires(stack_pred(stack, ?_values))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
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