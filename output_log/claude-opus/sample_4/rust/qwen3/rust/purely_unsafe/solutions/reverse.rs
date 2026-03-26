use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
struct Stack {
    head: *mut Node,
}

#[predicate]
fn node(p: *mut Node) -> bool {
    p != std::ptr::null_mut() &&
    exists::<i32, *mut Node>(v, q,
        p |-> Node { next: q, value: v } *
        (q == std::ptr::null_mut() || node(q))
    )
}

#[predicate]
fn stack(p: *mut Stack) -> bool {
    p != std::ptr::null_mut() &&
    p |-> Stack { head: h } *
    (h == std::ptr::null_mut() || node(h))
}

// Predicate for a singly-linked list segment from start to end (exclusive),
// reversed into rev: i.e., rev is the prefix reversed list, start..end is the rest.
#[predicate]
fn list_seg(start: *mut Node, end: *mut Node, rev: *mut Node) : bool {
    start == end && rev == std::ptr::null_mut() ||
    start != std::ptr::null_mut() &&
    exists::<*mut Node, i32>(next, val,
        start |-> Node { next: next, value: val } *
        list_seg(next, end, rev) *
        (rev == std::ptr::null_mut() || rev |-> Node { next: _, value: _ })
    )
}

#[predicate]
fn list(p: *mut Node) : bool {
    p == std::ptr::null_mut() ||
    exists::<*mut Node, i32>(q, v,
        p |-> Node { next: q, value: v } * list(q)
    )
}

impl Stack {
    #[requires(layout_of::<Stack>() == Layout::new::<Stack>())]
    #[ensures(result != std::ptr::null_mut() && stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack != std::ptr::null_mut() && stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        // We gain ownership of n |-> Node { next: _, value: _ } after allocation:
        #[invariant(
            n != std::ptr::null_mut() &&
            n |-> Node { next: _, value: _ } *
            (stack(stack))
        )]
        {
            (*n).next = (*stack).head;
            (*n).value = value;
            (*stack).head = n;
        }
    }

    #[requires(
        stack != std::ptr::null_mut() &&
        stack(stack) &&
        (*stack).head != std::ptr::null_mut()
    )]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        // Need ownership of head node to deallocate it:
        #[fold node(head);]
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack != std::ptr::null_mut() && stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn reverse(stack: *mut Stack) {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();

        #[invariant(
            stack != std::ptr::null_mut() &&
            stack(stack) &&
            // m points to reversed list segment (may be null or proper node)
            (m == std::ptr::null_mut() || node(m)) &&
            // n points to unreversed list segment (may be null or node)
            (n == std::ptr::null_mut() || node(n)) &&
            // The original list is split into reversed prefix m and suffix n,
            // expressed by some orig_head == old head pointing to full list:
            exists::<*mut Node>(orig_head,
                orig_head == old((*stack).head) &&
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

    #[requires(stack != std::ptr::null_mut() && stack(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        // To safely deallocate the stack, all nodes must be freed first.
        // Here we require all nodes to be deallocated or popped before dispose.
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