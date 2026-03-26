use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

predicate malloc_block_Node(p: *mut Node) = malloc_block(p, sizeof<Node>());
predicate malloc_block_Stack(p: *mut Stack) = malloc_block(p, sizeof<Stack>());
predicate pointer<T>(p: *mut T, v: T) = p |-> v;

predicate nodes(n: *mut Node) = 
    n == std::ptr::null_mut::<Node>() ?
        true
    :
        (*n).next |-> ?next &*& (*n).value |-> ?v &*& malloc_block_Node(n) &*& nodes(next);

predicate stack(s: *mut Stack) = 
    (*s).head |-> ?h &*& nodes(h) &*& malloc_block_Stack(s);

predicate pred_spec(p: I32Predicate) = is_I32Predicate(p) == true;

predicate pointer_to_nodes(n: *mut *mut Node) =
    pointer(n, ?node) &*& nodes(node);

#[requires(pointer_to_nodes(n) &*& pred_spec(p))]
#[ensures(pointer_to_nodes(n) &*& pred_spec(p))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate) {
    if !(*n).is_null() {
        let keep = p((**n).value);
        if keep {
            filter_nodes(&raw mut (**n).next, p);
        } else {
            let next_ = (**n).next;
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
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
    #[requires(true)]
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

    #[requires(stack(stack) &*& (*stack).head != std::ptr::null_mut::<Node>())]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack(stack) &*& pred_spec(p))]
    #[ensures(stack(stack) &*& pred_spec(p))]
    unsafe fn filter(stack: *mut Stack, p: I32Predicate) {
        filter_nodes(&raw mut (*stack).head, p);
    }

    #[requires(stack(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[requires(true)]
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