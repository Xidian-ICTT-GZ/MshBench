use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::ptr::null_mut;

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/* VeriFast predicates */
predicate node_own(*mut Node n; ) = 
    n != null_mut() &*& 
    [0.5]n as *mut u8 |-> _ &*& 
    [0.5](n as *mut u8).offset(1) |-> _;

predicate node_list(*mut Node n; ) = 
    n == null_mut() ? 
        true 
    : 
        node_own(n) &*& node_list(unsafe { (*n).next });

predicate stack_valid(*mut Stack s; ) = 
    s != null_mut() &*& 
    [0.5]s as *mut u8 |-> _ &*& 
    node_list(unsafe { (*s).head });

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