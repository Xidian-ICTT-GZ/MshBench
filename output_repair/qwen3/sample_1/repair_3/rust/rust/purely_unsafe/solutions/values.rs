use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node_own(*mut Node n; i32 value, *mut Node next) =
    n as *mut u8 |-> _ &*& (n as *mut u8).offset(1) as *mut i32 |-> value &*& n as *mut *mut Node |-> next;

predicate node_list(*mut Node n;) =
    if n == null_mut() then true else
        exists(?value, ?next) &*& node_own(n, value, next) &*& node_list(next);

predicate stack_valid(*mut Stack s;) =
    s as *mut *mut Node |-> ?head &*& node_list(head);

impl Stack {
    #[requires(true)]
    #[ensures(stack_valid(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack_valid(stack))]
    #[ensures(stack_valid(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_valid(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}