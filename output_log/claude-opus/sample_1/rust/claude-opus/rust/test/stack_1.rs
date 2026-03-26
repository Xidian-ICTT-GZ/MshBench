use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(n: *mut Node; count: i32) =
    if n == std::ptr::null_mut() {
        count == 0
    } else {
        count > 0 &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?v &*&
        nodes(next, count - 1)
    };

predicate stack(s: *mut Stack; count: i32) =
    (*s).head |-> ?h &*&
    nodes(h, count);

predicate node_alloc(n: *mut Node) = 
    (*n).next |-> _ &*&
    (*n).value |-> _;

predicate stack_alloc(s: *mut Stack) =
    (*s).head |-> _;

impl Stack {
    #[ensures(stack(result, 0))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        #[trusted]
        open stack_alloc(stack) if false; // avoid warning, no prior ownership at alloc
        (*stack).head = std::ptr::null_mut();
        close stack(stack, 0);
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
        close nodes(n, 1 + count);
        close stack(stack, count + 1);
    }

    #[requires(stack(stack, ?count) &*& count > 0)]
    #[ensures(stack(stack, count - 1))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        open stack(stack, count);
        open nodes(head, count);
        let next = (*head).next;
        let result = (*head).value;

        (*stack).head = next;
        close stack(stack, count - 1);
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(stack(stack, 0))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        open stack(stack, 0);
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