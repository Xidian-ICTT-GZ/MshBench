use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

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
    n.is_null() ? true : node(n, ?next, _) &*& nodes(next)
}

predicate stack(s: *mut Stack) {
    struct_Stack { head: ?h } @ s &*& nodes(h)
}

impl Stack {
    #[requires(layout.size() == std::mem::size_of::<Stack>())]
    #[requires(layout.align() == std::mem::align_of::<Stack>())]
    #[ensures(result.is_null() ? true : stack(result))]
    unsafe fn create() -> *mut Stack {
        let layout = Layout::new::<Stack>();
        let stack = alloc(layout) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(layout);
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }
    
    #[requires(stack(stack))]
    #[requires(layout.size() == std::mem::size_of::<Node>())]
    #[requires(layout.align() == std::mem::align_of::<Node>())]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let layout = Layout::new::<Node>();
        let n = alloc(layout) as *mut Node;
        if n.is_null() {
            handle_alloc_error(layout);
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }
    
    #[requires(stack(stack))]
    #[requires(layout.size() == std::mem::size_of::<Stack>())]
    #[requires(layout.align() == std::mem::align_of::<Stack>())]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        let layout = Layout::new::<Stack>();
        dealloc(stack as *mut u8, layout);
    }
}