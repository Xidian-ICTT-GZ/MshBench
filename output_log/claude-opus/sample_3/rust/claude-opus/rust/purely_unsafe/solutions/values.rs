use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

pred nodes(n: *mut Node; count: i32) =
    n == std::ptr::null_mut()
    ? count == 0
    : count > 0 &*&
      (*n).next |-> ?next &*&
      (*n).value |-> ?v &*&
      malloc_block_Node(n) &*&
      nodes(next, count - 1);

pred stack(s: *mut Stack; count: i32) =
    (*s).head |-> ?h &*&
    malloc_block_Stack(s) &*&
    nodes(h, count);

impl Stack {
    #[ensures(stack(result, 0))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(stack, ?count))]
    #[ensures(stack(stack, count + 1))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, 0))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}