use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(n: *mut Node; next: *mut Node, value: i32) {
    n != std::ptr::null_mut() && struct_alloc_points_to(n, Node { next, value })
}

predicate nodes(n: *mut Node; count: i32) {
    if n == std::ptr::null_mut() {
        count == 0
    } else {
        node(n, ?next, ?value) &*& nodes(next, ?c) &*& count == c + 1
    }
}

predicate stack(s: *mut Stack; head: *mut Node) {
    s != std::ptr::null_mut() && struct_alloc_points_to(s, Stack { head })
}

predicate full_stack(s: *mut Stack) {
    stack(s, ?head) &*& nodes(head, ?count)
}

impl Stack {
    #[requires(true)]
    #[ensures(result != std::ptr::null_mut() && stack(result, std::ptr::null_mut()))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(full_stack(stack))]
    #[ensures(full_stack(stack) && result >= 0)]
    unsafe fn get_count(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let mut n = head;
        let mut i = 0;
        #[invariant(nodes(n, ?rem) &*& nodes(head, ?total) &*& total == i + rem)]
        loop {
            if n.is_null() {
                break;
            }
            n = (*n).next;
            i += 1;
        }
        i
    }

    #[requires(full_stack(stack) && full_stack(other))]
    #[ensures(full_stack(stack))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        if !n.is_null() {
            #[invariant(nodes(n, ?rem) &*& nodes(head0, ?total) &*& total > 0 && rem >= 0)]
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

    #[requires(full_stack(stack))]
    #[ensures(full_stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(full_stack(stack) && (*stack).head != std::ptr::null_mut())]
    #[ensures(full_stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(full_stack(stack))]
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