use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[predicate]
fn node(p: *mut Node) = 
    p != std::ptr::null_mut() &*&
    exists::<i32, *mut Node>(v, q,
        p |-> Node { next: q, value: v } &*&
        (q == std::ptr::null_mut() || node(q))
    );

#[predicate]
fn stack(p: *mut Stack) = 
    p != std::ptr::null_mut() &*&
    p |-> Stack { head: ?h } &*&
    (h == std::ptr::null_mut() || node(h));

#[predicate]
fn list_seg(start: *mut Node, end: *mut Node, rev: *mut Node) =
    start == end &*& rev == std::ptr::null_mut() 
    ||
    start != std::ptr::null_mut() &*&
    exists::<*mut Node, i32>(next, val,
        start |-> Node { next: next, value: val } &*&
        list_seg(next, end, rev) &*&
        (rev == std::ptr::null_mut() || rev |-> Node { next: _, value: _ })
    );

#[predicate]
fn list(p: *mut Node) =
    p == std::ptr::null_mut() 
    ||
    exists::<*mut Node, i32>(q, v,
        p |-> Node { next: q, value: v } &*&
        list(q)
    );

impl Stack {
    #[requires(layout_of::<Stack>() == Layout::new::<Stack>())]
    #[ensures(result != std::ptr::null_mut() &*& stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack != std::ptr::null_mut() &*& stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        n |-> _; // Get full ownership of freshly allocated node

        #[invariant(
            n != std::ptr::null_mut() &*&
            exists::<*mut Node, i32>(old_next, old_val,
                n |-> Node { next: old_next, value: old_val }
            )
        )]
        {
            (*n).next = (*stack).head;
            (*n).value = value;
            (*stack).head = n;
        }
        // After modification, stack predicate is re-established:
        // old stack(stack) = stack(stack) but now with new node
    }

    #[requires(stack != std::ptr::null_mut() &*& stack(stack) &*& (*stack).head != std::ptr::null_mut())]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        head |-> Node { next: (*head).next, value: (*head).value };

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack != std::ptr::null_mut() &*& stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn reverse(stack: *mut Stack) {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();

        #[invariant(
            stack(stack) &*&
            (n == std::ptr::null_mut() ? true : node(n)) &*&
            (m == std::ptr::null_mut() || node(m)) &*&
            exists::<*mut Node>(orig_head,
                orig_head == (*stack).head &*&
                list_seg(orig_head, n, m)
            )
        )]
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

    #[requires(stack != std::ptr::null_mut() &*& stack(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        stack |-> Stack { head: ?h } &*&
        (h == std::ptr::null_mut() || node(h));
        // Need to ensure nodes are freed before calling dispose.
        // This example just deallocates the stack struct,
        // assuming stack is empty or already cleaned.

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

        Stack::reverse(s);
        Stack::dispose(s);
    }
}

#[repr(C)]
pub struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
pub struct Stack {
    head: *mut Node,
}

// Layout helpers for VeriFast
#[pure]
fn layout_of<T>() -> Layout {
    Layout::new::<T>()
}