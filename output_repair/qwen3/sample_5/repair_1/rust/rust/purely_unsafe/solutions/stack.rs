use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node_own(*mut Node n, *mut Node next, i32 value) {
    n != null && [n]..Node { next: next, value: value }
}

predicate stack_own(*mut Stack s, *mut Node head) {
    s != null && [s]..Stack { head: head }
}

predicate stack_list(*mut Node head) {
    head == null ||
    exists *mut Node next, i32 value ::
        node_own(head, next, value) * stack_list(next)
}

impl Stack {
    #[ensures(stack_own(result, null) * stack_list(null))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack_own(stack, ?head) * stack_list(head))]
    #[ensures(stack_own(stack, ?new_head) * node_own(new_head, head, value) * stack_list(new_head))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_own(stack, ?head) * head != null * exists *mut Node next, i32 v :: node_own(head, next, v) * stack_list(next))]
    #[ensures(stack_own(stack, ?new_head) * stack_list(new_head))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack_own(stack, ?head) * stack_list(head))]
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
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}