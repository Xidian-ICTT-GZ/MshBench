use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_list(n: *mut Node) -> bool {
    match n as usize {
        0 => true,
        _ => {
            let next = unsafe { (*n).next };
            node_list(next)
        }
    }
}

#[predicate]
fn stack_owns(s: *mut Stack) -> bool {
    let head = unsafe { (*s).head };
    node_list(head)
}

impl Stack {
    #[ensures(result as usize != 0)]
    #[ensures(stack_owns(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack_owns(stack))]
    #[ensures(stack_owns(stack))]
    unsafe fn get_count(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let mut n = head;
        let mut i = 0;

        loop {
            if n.is_null() {
                break;
            }

            n = (*n).next;
            i += 1;
        }

        i
    }

    #[requires(stack_owns(stack))]
    #[requires(stack_owns(other))]
    #[ensures(stack_owns(stack))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            loop {
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
            }

            (*n).next = (*stack).head;

            (*stack).head = head0;
        }
    }

    #[requires(stack_owns(stack))]
    #[ensures(stack_owns(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_owns(stack))]
    #[ensures(stack_owns(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack_owns(stack))]
    unsafe fn dispose(stack: *mut Stack) {
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