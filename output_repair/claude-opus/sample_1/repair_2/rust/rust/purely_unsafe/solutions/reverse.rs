use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node_own(n: *mut Node) = n != std::ptr::null_mut();

predicate stack_own(s: *mut Stack) = s != std::ptr::null_mut();

predicate list_own(n: *mut Node) =
    n == std::ptr::null_mut() ||
    (n != std::ptr::null_mut() && node_own(n) && list_own((*n).next));

impl Stack {
    #[requires(true)]
    #[ensures(stack_own(result) && list_own((*result).head))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack_own(stack) && list_own((*stack).head))]
    #[ensures(stack_own(stack) && list_own((*stack).head))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_own(stack) && list_own((*stack).head) && (*stack).head != std::ptr::null_mut())]
    #[ensures(stack_own(stack) && list_own((*stack).head))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack_own(stack) && list_own((*stack).head))]
    #[ensures(stack_own(stack) && list_own((*stack).head))]
    unsafe fn reverse(stack: *mut Stack) {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();

        #[invariant(list_own(n) && list_own(m))]
        loop {
            if n.is_null() {
                break;
            }

            let next = (*n).next;

            (*n).next = m;
            m = n;
            n = next;
        }

        (*stack).head = m;
    }

    #[requires(stack_own(stack) && list_own((*stack).head))]
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
        let _result1 = Stack::pop(s);

        let _result2 = Stack::pop(s);

        Stack::dispose(s);
    }
}