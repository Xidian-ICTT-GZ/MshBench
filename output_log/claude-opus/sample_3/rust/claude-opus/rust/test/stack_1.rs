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

impl Stack {
    #[ensures(stack(result, 0))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        #[ghost] // allocate and initialize stack predicate ownership
        assume(stack != std::ptr::null_mut());
        #[predicate] predicate stack_state(s: *mut Stack) = (*s).head |-> std::ptr::null_mut();
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
        #[ghost] assume(n != std::ptr::null_mut());
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }
    #[requires(stack(stack, ?count) &*& count > 0)]
    #[ensures(stack(stack, count - 1))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        #[requires((*head).next |-> ?next &*& (*head).value |-> ?v &*& nodes(next, count - 1))]
        #[ensures(nodes(next, count - 1))]
        #[ensures(result == v)]
        fn take_node(head: *mut Node) -> i32 {
            open nodes(head, _);
            let v = (*head).value;
            close nodes((*head).next, count - 1);
            v
        }
        let result = take_node(head);
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }
    #[requires(stack(stack, 0))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
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