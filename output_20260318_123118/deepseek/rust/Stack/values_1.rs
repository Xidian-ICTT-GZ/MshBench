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
    if n.is_null() {
        emp
    } else {
        let next = (*n).next;
        let value = (*n).value;
        node(n, next, value) * nodes(next)
    }
}

predicate stack(s: *mut Stack) {
    let head = (*s).head;
    struct_Stack { head: head } @ s * nodes(head)
}

impl Stack {
    #[requires(Layout::new::<Stack>().size() > 0)]
    #[ensures(result != std::ptr::null_mut())]
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(stack(stack))]
    #[requires(Layout::new::<Node>().size() > 0)]
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
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}