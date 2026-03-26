use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn nodes(n: *mut Node) -> bool {
    if n.is_null() {
        true
    } else {
        let node = unsafe { &*n };
        ptr::from_ref(node).is_some() && node.next.is_null()
    }
}

#[predicate]
fn stack(s: *mut Stack) -> bool {
    if s.is_null() {
        false
    } else {
        let stack = unsafe { &*s };
        ptr::from_ref(stack).is_some() && stack.head.is_null()
    }
}

unsafe fn dispose_nodes(n: *mut Node) {
    #[requires(nodes(n))]
    #[ensures(true)]
    if !n.is_null() {
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[ensures(result != 0 && stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        return stack;
    }

    #[requires(stack(stack))]
    #[ensures(result == (*stack).head.is_null())]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        return result;
    }

    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack) && !(*stack).head.is_null())]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        return result;
    }

    #[requires(stack(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dispose_nodes((*stack).head);
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