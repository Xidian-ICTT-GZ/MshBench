use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node(n: *mut Node) = n != std::ptr::null_mut() &*&
    malloc_block::<Node>(n) &*&
    n->Node { next: ?next, value: ?value };

#[predicate]
fn stack(s: *mut Stack) = s != std::ptr::null_mut() &*&
    malloc_block::<Stack>(s) &*&
    s->Stack { head: ?head } &*&
    stack_nodes(head);

#[predicate]
fn stack_nodes(n: *mut Node) = 
    if n == std::ptr::null_mut() {
        emp
    } else {
        node(n) &*& stack_nodes((*n).next)
    };

impl Stack {
    #[requires(true)]
    #[ensures(result != std::ptr::null_mut() && stack(result) && malloc_block::<Stack>(result))]
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
        open stack(stack);
        let head = (*stack).head;
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = head;
        (*n).value = value;
        (*stack).head = n;
        close node(n);
        close stack_nodes(n);
        close stack(stack);
    }

    #[requires(stack != std::ptr::null_mut() && stack(stack))]
    #[requires((*stack).head != std::ptr::null_mut())]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        open stack(stack);
        let head = (*stack).head;
        open node(head);
        let value = (*head).value;
        let next = (*head).next;
        (*stack).head = next;
        close stack_nodes(next);
        close stack(stack);
        dealloc(head as *mut u8, Layout::new::<Node>());
        value
    }

    #[requires(stack != std::ptr::null_mut() && stack(stack))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        open stack(stack);
        open stack_nodes((*stack).head);
        // All nodes deallocated
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}