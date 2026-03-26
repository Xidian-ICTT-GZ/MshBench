use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(ptr: *mut Node, len: i32) =
    if len == 0 {
        ptr.is_null()
    } else {
        ptr != std::ptr::null_mut() &&
        Owned(ptr) &&
        Owned((*ptr).next) &&
        node_list((*ptr).next, len - 1)
    };

#[requires(node_list(nodes, _))]
#[ensures(true)]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    #[ensures(Owned(result) && Owned((*result).head) && (*result).head.is_null())]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(Owned(stack) && Owned((*stack).head))]
    #[ensures(true)]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        let _head = (*stack).head;

        let result = (*stack).head.is_null();

        result
    }

    #[requires(Owned(stack) && Owned((*stack).head) && node_list((*stack).head, _))]
    #[ensures(true)]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }

    #[requires(Owned(stack) && Owned((*stack).head))]
    #[ensures(Owned(stack) && Owned((*stack).head))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(Owned(stack) && Owned((*stack).head) && (*stack).head != std::ptr::null_mut())]
    #[ensures(Owned(stack) && Owned((*stack).head))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(Owned(stack) && Owned((*stack).head) && n >= 0)]
    #[ensures(Owned(stack) && Owned((*stack).head))]
    unsafe fn popn(stack: *mut Stack, n: i32) {
        let mut i = 0;
        loop {
            #[invariant(Owned(stack) && Owned((*stack).head) && i >= 0 && i <= n)]
            {
                if i == n {
                    break;
                }
                Stack::pop(stack);
                i += 1;
            }
        }
    }

    #[requires(Owned(stack) && Owned((*stack).head) && node_list((*stack).head, _))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        let mut n = (*stack).head;
        loop {
            #[invariant(node_list(n, _))]
            {
                if n.is_null() {
                    break;
                }

                let next = (*n).next;
                dealloc(n as *mut u8, Layout::new::<Node>());
                n = next;
            }
        }

        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}