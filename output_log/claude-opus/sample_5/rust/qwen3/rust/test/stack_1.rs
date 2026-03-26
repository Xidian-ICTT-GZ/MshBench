use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
struct Stack {
    head: *mut Node,
}

predicate node(struct Node* n; *mut Node next, int value) =
    malloc_block(n, sizeof(struct Node)) &*&
    n->next |-> next &*&
    n->value |-> value;

predicate stack(struct Stack* s; *mut Node head) =
    malloc_block(s, sizeof(struct Stack)) &*&
    s->head |-> head;

/* Create an empty stack */
impl Stack {
    #[requires(true)]
    #[ensures(result != std::ptr::null_mut() && stack(result, std::ptr::null_mut()))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack != std::ptr::null_mut() && stack(stack, head))]
    #[ensures(stack(stack, n) &*& node(n, head, value))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack != std::ptr::null_mut() && stack(stack, head) && head != std::ptr::null_mut() && node(head, next, val))]
    #[ensures(stack(stack, next) &*& result == val)]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack != std::ptr::null_mut() && stack(stack, head))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        // recursively dispose nodes
        let mut cur = (*stack).head;
        while (cur != std::ptr::null_mut())
            invariant(stack(stack, (*stack).head) &*& cur == (*stack).head;)
        {
            let next = (*cur).next;
            dealloc(cur as *mut u8, Layout::new::<Node>());
            (*stack).head = next;
            cur = next;
        }
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