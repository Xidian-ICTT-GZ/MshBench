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
        Node(n; ?v, ?nxt) &*& Nodes(nxt);

predicate Stack(s: *mut Stack) =
    s != std::ptr::null_mut() &*&
    (*s).head |-> ?h &*& Nodes(h);

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
        // Before allocation, we own Stack(stack) = head|->h & Nodes(h)
        let h = (*stack).head;
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        // After allocation, we have fresh Node(n) with uninitialized fields
        // Initialize Node(n) = n->value = value, n->next = h
        (*n).next = h;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(Stack(stack) &*& (*stack).head != std::ptr::null_mut())]
    #[ensures(Stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        // Pre: Stack(stack) = head|->h & Nodes(h)
        // and h != null
        let head = (*stack).head;
        // head points to Node(head) = v, nxt
        // We have ownership of Node(head)
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(Stack(stack) &*& (*stack).head == std::ptr::null_mut())]
    unsafe fn dispose(stack: *mut Stack) {
        // Pre: Stack(stack) with empty list (head == null), so no Nodes owned
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);

        let result2 = Stack::pop(s);

        Stack::dispose(s);
    }
}