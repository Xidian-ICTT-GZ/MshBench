use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

predicate nodes(n: *mut Node;) =
    n == std::ptr::null_mut() ?
        true
    :
        (*n).next |-> ?next
        &*& (*n).value |-> ?v
        &*& malloc_block_Node(n)
        &*& nodes(next)
    ;

// ownership invariant for stack: owns head pointer and malloc block for Stack struct and linked list nodes reachable from head
predicate stack(s: *mut Stack;) =
    (*s).head |-> ?h
    &*& malloc_block_Stack(s)
    &*& nodes(h)
    ;

// abstract predicate describing ownership and permission of predicate pointer p, relates to function pointer p with shared readonly permission
predicate_ctor predicate_req(p: I32Predicate)(v: int) = 
    [_]is_I32Predicate(p) &*& true; // pure fact combined with readonly permission on p

predicate_ctor predicate_ens(p: I32Predicate)(v: int; r: bool) = 
    true; // no heap ownership so pure

#[requires(nodes(n) &*& [_]is_I32Predicate(p))]
#[ensures(nodes(result))]
unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node {
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);

            (*n).next = next;

            n
        } else {
            next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
    }
}

#[requires(nodes(n))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack(stack) &*& [_]is_I32Predicate(p))]
    #[ensures(stack(stack))]
    unsafe fn filter(stack: *mut Stack, p: I32Predicate) {
        let head = filter_nodes((*stack).head, p);

        (*stack).head = head;
    }

    #[requires(stack(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[ensures(true)]
unsafe fn neq_20(x: i32) -> bool {
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}