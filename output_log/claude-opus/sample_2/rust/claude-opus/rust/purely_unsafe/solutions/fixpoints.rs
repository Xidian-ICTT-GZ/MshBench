use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate Node(n: *mut Node; v: i32, nxt: *mut Node) =
    (*n).value |-> v &*& (*n).next |-> nxt;

predicate Nodes(n: *mut Node) =
    n == std::ptr::null_mut() ?
        true
    :
        Node(n, ?v, ?nxt) &*& Nodes(nxt);

predicate Stack(s: *mut Stack) =
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
        fixpoint Nodes splitNodes(Nodes ns) {
          switch(ns) {
            case true: return Pair(nil(),nil());
            case Node(n,v,nxt) &*& Nodes(nxt): return Pair(Node(n,v,nxt), Nodes(nxt));
          }
        }

        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(Stack(stack) &*& (*stack).head != std::ptr::null_mut())]
    #[ensures(Stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        unfold Nodes(head);
        open Node(head, ?v, ?next);

        (*stack).head = next;

        fold Nodes(next);
        fold Stack(stack);

        let result = (*head).value;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(Stack(stack) &*& (*stack).head == std::ptr::null_mut())]
    unsafe fn dispose(stack: *mut Stack) {
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