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
    n != std::ptr::null_mut(),
{
    requires!(
        node(n) == NodePred { next: (*n).next, value: (*n).value }
    );
    ensures!(
        node(n) == NodePred { next: (*n).next, value: (*n).value }
    );
    true
}

#[lemma]
fn stack_pred_inv(s: *mut Stack) -> bool
where
    s != std::ptr::null_mut(),
{
    requires!(
        stack(s) == StackPred { head: (*s).head }
    );
    ensures!(
        stack(s) == StackPred { head: (*s).head }
    );
    true
}

impl Stack {
    #[requires(
        true
    )]
    #[ensures(
        result != std::ptr::null_mut() && 
        stack(result) == StackPred { head: std::ptr::null_mut() } &&
        malloc_block(result as *mut u8, Layout::new::<Stack>())
    )]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(
        stack != std::ptr::null_mut() &&
        stack(stack) == StackPred { head: head } &&
        malloc_block(stack as *mut u8, Layout::new::<Stack>())
    )]
    #[ensures(
        stack(stack) == StackPred { head: new_head } &&
        malloc_block(stack as *mut u8, Layout::new::<Stack>()) &&
        malloc_block(n as *mut u8, Layout::new::<Node>()) &&
        node(n) == NodePred { next: head, value: value }
    )]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(
        stack != std::ptr::null_mut() &&
        stack(stack) == StackPred { head: head } &&
        head != std::ptr::null_mut() &&
        malloc_block(stack as *mut u8, Layout::new::<Stack>()) &&
        malloc_block(head as *mut u8, Layout::new::<Node>()) &&
        node(head) == NodePred { next: next, value: val }
    )]
    #[ensures(
        result == val &&
        stack(stack) == StackPred { head: next } &&
        malloc_block(stack as *mut u8, Layout::new::<Stack>())
    )]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(
        stack != std::ptr::null_mut() &&
        stack(stack) == StackPred { head: head } &&
        malloc_block(stack as *mut u8, Layout::new::<Stack>())
    )]
    #[ensures(
        true
    )]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}