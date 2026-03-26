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
fn nodes(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        let node = unsafe { &*n };
        nodes(node.next) && true
    }
}

#[predicate]
fn nodes_with_value(n: *mut Node, v: i32) -> bool {
    if n.is_null() {
        true
    } else {
        let node = unsafe { &*n };
        node.value == v && nodes_with_value(node.next, v)
    }
}

#[predicate]
fn stack(s: *mut Stack) -> bool {
    if s.is_null() {
        false
    } else {
        let stack = unsafe { &*s };
        nodes(stack.head) && true
    }
}

#[predicate]
fn stack_with_head(s: *mut Stack, h: *mut Node) -> bool {
    if s.is_null() {
        false
    } else {
        let stack = unsafe { &*s };
        stack.head == h && nodes(h) && true
    }
}

#[predicate]
fn predicate_holds(p: I32Predicate, x: i32) -> bool {
    unsafe { p(x) }
}

#[predicate]
fn predicate_true_for_all(p: I32Predicate, n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        let node = unsafe { &*n };
        predicate_holds(p, node.value) && predicate_true_for_all(p, node.next)
    }
}

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node {
    #[requires(nodes(n))]
    #[ensures(|result| nodes(result) && predicate_true_for_all(p, result))]
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
    #[requires(nodes(n))]
    #[ensures(true)]
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack {
        #[ensures(|result| stack(result))]
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32) {
        #[requires(stack(stack))]
        #[ensures(|stack| stack_with_head(stack, old((*stack).head)) && nodes_with_value(old((*stack).head), value))]
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32 {
        #[requires(|stack| stack_with_head(stack, old((*stack).head)) && !old((*stack).head).is_null())]
        #[ensures(|result, stack| stack(stack) && result == old((*((*stack).head)).value))]
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate) {
        #[requires(stack(stack))]
        #[ensures(|stack| stack(stack) && predicate_true_for_all(p, (*stack).head))]
        let head = filter_nodes((*stack).head, p);

        (*stack).head = head;
    }

    unsafe fn dispose(stack: *mut Stack) {
        #[requires(stack(stack))]
        #[ensures(true)]
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool {
    #[ensures(|result| result == (x != 20))]
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