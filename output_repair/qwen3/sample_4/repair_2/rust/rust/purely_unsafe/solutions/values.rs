use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node_own(*mut Node n, *mut Node next, i32 value) =
    n as *mut u8 |-> (next as usize) &*&
    (n as usize + std::mem::size_of::<*mut Node>()) as *mut i32 |-> value;

predicate stack_own(*mut Stack s, *mut Node head) =
    s as *mut *mut Node |-> head;

predicate node_list(*mut Node n) =
    n == null_mut() ?
        emp
    :
        exists<*mut Node, i32>(?next, ?val) &*&
        node_own(n, next, val) &*&
        node_list(next);

predicate stack_valid(*mut Stack s) =
    exists<*mut Node>(?head) &*&
    stack_own(s, head) &*&
    node_list(head);

impl Stack {
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
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}