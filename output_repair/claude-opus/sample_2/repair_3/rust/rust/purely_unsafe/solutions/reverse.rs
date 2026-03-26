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
        ptr == std::ptr::null_mut()
    } else {
        ptr != std::ptr::null_mut() &&
        exists(next_ptr: *mut Node, val: i32) {
            *ptr == Node { next: next_ptr, value: val } &&
            node_list(next_ptr, len - 1)
        }
    };

predicate stack_inv(stack: *mut Stack, len: i32) =
    stack != std::ptr::null_mut() &&
    exists(head: *mut Node) {
        *stack == Stack { head: head } &&
        node_list(head, len)
    };

impl Stack {
    #[ensures(result != std::ptr::null_mut() && stack_inv(result, 0))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack_inv(stack, len) && len >= 0)]
    #[ensures(stack_inv(stack, len + 1))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_inv(stack, len) && len > 0)]
    #[ensures(stack_inv(stack, len - 1))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack_inv(stack, len) && len >= 0)]
    #[ensures(stack_inv(stack, len))]
    unsafe fn reverse(stack: *mut Stack) {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();

        loop {
            #[invariant(node_list(n, n_len) && node_list(m, m_len) && n_len + m_len == len)]
            {
                if n.is_null() {
                    break;
                }

                let next = (*n).next;

                (*n).next = m;
                m = n;
                n = next;
            }
        }

        (*stack).head = m;
    }

    #[requires(stack_inv(stack, len) && len >= 0)]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);

        let result2 = Stack::pop(s);

        Stack::dispose(s);
    }
}