use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {
    #[requires(true)]
    #[ensures(exists(h: *mut Node) {
        result->Stack { head: h } &*& h.is_null()
    })]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(exists(h: *mut Node) {
        stack->Stack { head: h }
    })]
    #[ensures(exists(h: *mut Node) {
        stack->Stack { head: h }
    })]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(exists(h: *mut Node) {
        stack->Stack { head: h } &*& 
        h->Node { next: _, value: _ }
    })]
    #[ensures(exists(h: *mut Node) {
        stack->Stack { head: h }
    })]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(exists(h: *mut Node) {
        stack->Stack { head: h }
    })]
    #[ensures(exists(h: *mut Node) {
        stack->Stack { head: h }
    })]
    unsafe fn reverse(stack: *mut Stack) {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();

        loop {
            #[invariant(exists(n_ptr: *mut Node, m_ptr: *mut Node) {
                n == n_ptr && m == m_ptr
            })]
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

    #[requires(exists(h: *mut Node) {
        stack->Stack { head: h }
    })]
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