use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred]
struct NodePred {
    next: *mut Node,
    value: i32,
}

#[pred]
struct StackPred {
    head: *mut Node,
}

#[lemma]
fn node_pred_inv(n: *mut Node) -> bool
where
    n: *mut Node,
{
    requires([
        n != std::ptr::null_mut() && node(n),
    ]);
    ensures([
        node(n) == NodePred { next: (*n).next, value: (*n).value },
    ]);
    // This lemma is trivial but necessary to connect heap predicate to struct fields.
    true
}

#[predicate]
fn node(p: *mut Node) -> bool {
    p != std::ptr::null_mut() &&
    exists::<i32, *mut Node>(v, q,
        p |-> Node { next: q, value: v } *
        node(q) ||
        q == std::ptr::null_mut()
    )
}

#[predicate]
fn stack(p: *mut Stack) -> bool {
    p != std::ptr::null_mut() &&
    p |-> Stack { head: h } *
    (h == std::ptr::null_mut() || node(h))
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
        // Acquire ownership of new node
        #[invariant(n != std::ptr::null_mut() && n |-> Node { next: _, value: _ })]
        {
            (*n).next = (*stack).head;
            (*n).value = value;
            (*stack).head = n;
        }
        // Now the stack owns the new node; update predicate
    }

    #[requires(stack != std::ptr::null_mut() && stack(stack) && (*stack).head != std::ptr::null_mut())]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

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

        // Loop invariant: n and m form a reversed prefix/suffix partition
        // Specifically: original list = m -> ... -> head -> n -> rest
        // where m points to reversed prefix, n points to unreversed suffix
        #[invariant(
            stack(stack) &&
            (n == std::ptr::null_mut() ==> m != std::ptr::null_mut() || (*stack).head == std::ptr::null_mut()) &&
            (m != std::ptr::null_mut() ==> node(m)) &&
            (n != std::ptr::null_mut() ==> node(n)) &&
            exists::<*mut Node>(orig_head,
                orig_head == (*stack).head &&
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
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

// Predicate for a singly-linked list segment from start to end (exclusive), reversed into rev
#[predicate]
fn list_seg(start: *mut Node, end: *mut Node, rev: *mut Node) -> bool {
    start == end && rev == std::ptr::null_mut() ||
    start != std::ptr::null_mut() &&
    exists::<*mut Node, i32>(next, val,
        start |-> Node { next: next, value: val } *
        list_seg(next, end, rev) *
        (rev == std::ptr::null_mut() || rev |-> Node { next: _, value: _ })
    )
}

// Helper: list from p to null is a proper linked list
#[predicate]
fn list(p: *mut Node) -> bool {
    p == std::ptr::null_mut() ||
    exists::<*mut Node, i32>(q, v,
        p |-> Node { next: q, value: v } * list(q)
    )
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