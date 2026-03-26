use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(n: *mut Node; next: *mut Node, value: i32) {
    struct_Node { next: next, value: value } @ n
}

predicate nodes(n: *mut Node) {
    n.is_null() ? true : node(n; let next = (*n).next, let val = (*n).value) * nodes(next)
}

predicate stack(s: *mut Stack) {
    struct_Stack { head: let h = (*s).head } @ s * nodes(h)
}

impl Stack {
    #[requires(Layout::new::<Stack>().size() > 0)]
    #[ensures(result.is_null() ? true : stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(stack(stack))]
    #[requires(!stack.is_null())]
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

    #[requires(stack(stack))]
    #[requires(!stack.is_null())]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}