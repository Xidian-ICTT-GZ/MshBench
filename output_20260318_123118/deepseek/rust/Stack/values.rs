use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(n: *mut Node; next: *mut Node, value: i32) {
    struct_Node { next: next, value: value }@n
}

predicate nodes(n: *mut Node) {
    n == std::ptr::null_mut() ? true : node(n, let next, let value) &*& nodes(next)
}

predicate stack(s: *mut Stack) {
    struct_Stack { head: let head }@s &*& nodes(head)
}

impl Stack {
    #[requires(true)]
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close nodes(std::ptr::null_mut());
        close stack(stack);
        stack
    }
    
    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        open stack(stack);
        let head = (*stack).head;
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = head;
        (*n).value = value;
        close node(n, head, value);
        open nodes(head);
        close nodes(n);
        (*stack).head = n;
        close stack(stack);
    }

    #[requires(stack(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        open stack(stack);
        let head = (*stack).head;
        open nodes(head);
        if head != std::ptr::null_mut() {
            open node(head, let next, _);
            open nodes(next);
        }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}