use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[pred]
pub predicate node_pred(Node* n;) =
    n != 0 && n->value |-> _ &*& n->next |-> _;

#[pred]
pub predicate stack_pred(Stack* s;) =
    s != 0 && s->head |-> ?h &*&
    (h == 0 || node_pred(h));

impl Stack {
    unsafe fn create() -> *mut Stack {
        #[requires(Layout::new::<Stack>().size() > 0)]
        #[ensures(result != 0)]
        #[ensures(stack_pred(result))]
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32) {
        #[requires(stack != 0)]
        #[requires(stack_pred(stack))]
        #[ensures(stack_pred(stack))]
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32 {
        #[requires(stack != 0)]
        #[requires(stack_pred(stack))]
        #[requires((*stack).head != std::ptr::null_mut())]
        #[ensures(stack_pred(stack))]
        #[ensures(result == old((*stack).head)->value)]
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack) {
        #[requires(stack != 0)]
        #[requires(stack_pred(stack))]
        #[requires((*stack).head == std::ptr::null_mut())]
        #[ensures(true)]
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