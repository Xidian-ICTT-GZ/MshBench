use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
pub struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
pub struct Stack {
    head: *mut Node,
}

#[predicate]
fn node(p: *mut Node) = p != std::ptr::null_mut() &*&
    p |-> Node { next: ?next, value: ?v } &*&
    (next == std::ptr::null_mut() || node(next));

#[predicate]
fn stack(s: *mut Stack) = s != std::ptr::null_mut() &*&
    s |-> Stack { head: ?h } &*&
    (h == std::ptr::null_mut() || node(h));

#[predicate]
fn list_seg(start: *mut Node, end: *mut Node, rev: *mut Node) = 
    (start == end &*& rev == std::ptr::null_mut()) 
    || 
    (start != std::ptr::null_mut() &*& 
     start |-> Node { next: ?next, value: ?val } &*& 
     list_seg(next, end, rev) &*&
     (rev == std::ptr::null_mut() || rev |-> Node { next: _, value: _ }));

#[predicate]
fn list(p: *mut Node) =
    p == std::ptr::null_mut() || exists<*mut Node, i32>(?q, ?v,
        p |-> Node { next: q, value: v } &*& list(q));

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

        // Allocate ownership for new node
        // We gain exclusive ownership of n here:
        #[invariant(n != std::ptr::null_mut() &*& n |-> Node { next: ?_, value: ?_ })]
        {
            (*n).next = (*stack).head;
            (*n).value = value;
            (*stack).head = n;
        }
    }

    #[requires(stack != std::ptr::null_mut() &*& stack(stack) &*& (*stack).head != std::ptr::null_mut())]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        // We must have full ownership of head node here
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
            // Original stack predicate holds throughout
            stack(stack) &*&
            // n and m partition linked list: n points to unreversed suffix, m to reversed prefix
            (n == std::ptr::null_mut() || node(n)) &*&
            (m == std::ptr::null_mut() || node(m)) &*&
            exists::<*mut Node>(?orig_head,
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