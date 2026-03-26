use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(n: *mut Node; next: *mut Node, value: i32) {
    addr_of!((*n).next) |-> next &*& addr_of!((*n).value) |-> value
}

predicate nodes(n: *mut Node; count: i32) {
    n.is_null() ? count == 0
    : node(n, ?next, ?_) &*& nodes(next, ?c) &*& count == c + 1
}

predicate stack(s: *mut Stack; head: *mut Node) {
    addr_of!((*s).head) |-> head
}

predicate full_stack(s: *mut Stack; count: i32) {
    stack(s, ?head) &*& nodes(head, count)
}

impl Stack {
    #[requires(true)]
    #[ensures(full_stack(result, 0))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(full_stack(stack, ?count))]
    #[ensures(full_stack(stack, count) &*& result == count)]
    unsafe fn get_count(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let mut n = head;
        let mut i = 0;

        #[invariant(full_stack(stack, ?c) &*& nodes(n, ?rem) &*& c == i + rem)]
        loop {
            if n.is_null() {
                break;
            }

            n = (*n).next;
            i += 1;
        }

        i
    }

    #[requires(full_stack(stack, ?c1) &*& full_stack(other, ?c2))]
    #[ensures(full_stack(stack, c1 + c2))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            #[invariant(nodes(n, ?rem) &*& nodes(head0, c2) &*& rem >= 1)]
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

    #[requires(full_stack(stack, ?count))]
    #[ensures(full_stack(stack, count + 1))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(full_stack(stack, ?count) &*& count >= 1)]
    #[ensures(full_stack(stack, count - 1) &*& result == ?v)]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(full_stack(stack, 0))]
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