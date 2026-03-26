use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

predicate node_list(*mut Node n;);

predicate stack_inv(*mut Stack s;) =
    exists(head: *mut Node) (
        Stack_head(s) |-> head &*& node_list(head)
    );

predicate node_list(*mut Node n;) =
    n == null() ? emp : (
        Node_next(n) |-> ?next &*& Node_value(n) |-> ?v &*& node_list(next)
    );

impl Stack {
    #[requires(true)]
    #[ensures(stack_inv(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn filter(stack: *mut Stack, p: I32Predicate) {
        let old_head = (*stack).head;
        let new_head = filter_nodes(old_head, p);
        (*stack).head = new_head;
    }

    #[requires(stack_inv(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        let head = (*stack).head;
        dispose_nodes(head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[requires(node_list(n))]
#[ensures(node_list(result))]
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

#[requires(node_list(n))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
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