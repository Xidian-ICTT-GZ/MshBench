use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate Node(n: *mut Node; v: i32, nxt: *mut Node) =
    n != std::ptr::null_mut() &*&
    (*n).value |-> v &*& (*n).next |-> nxt;

predicate Nodes(n: *mut Node) =
    n == std::ptr::null_mut() ?
        true
    :
        Node(n, ?v, ?nxt) &*& Nodes(nxt);

predicate Stack(s: *mut Stack) =
    s != std::ptr::null_mut() &*& (*s).head |-> ?h &*& Nodes(h);

impl Stack {
    #[ensures(Stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(Stack(stack))]
    #[ensures(Stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        // Before mutation we have ownership of stack and the linked nodes
        // Need to consume Nodes(h) and produce Nodes(n)
        // Destructure current nodes
        open Stack(stack);
        let old_head = (*stack).head;
        open Nodes(old_head);

        (*n).next = old_head;
        (*n).value = value;
        (*stack).head = n;

        close Node(n, value, old_head);
        close Nodes(n);
        close Stack(stack);
    }

    #[requires(Stack(stack) &*& (*stack).head != std::ptr::null_mut())]
    #[ensures(Stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        open Stack(stack);
        let head = (*stack).head;
        open Nodes(head);
        open Node(head, ?v, ?nxt);

        (*stack).head = nxt;

        close Nodes(nxt);
        close Stack(stack);

        dealloc(head as *mut u8, Layout::new::<Node>());

        v
    }

    #[requires(Stack(stack) &*& (*stack).head == std::ptr::null_mut())]
    unsafe fn dispose(stack: *mut Stack) {
        open Stack(stack);
        // Since head == null, Nodes(head) = true, no heap allocated nodes remain.
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