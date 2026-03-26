use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node(n: *mut Node, next: *mut Node, value: i32) =
    n != std::ptr::null_mut() &*&
    malloc_block(n as *mut u8, Layout::new::<Node>()) &*&
    n->next |-> next &*&
    n->value |-> value;

#[predicate]
fn stack(s: *mut Stack, head: *mut Node) =
    s != std::ptr::null_mut() &*&
    malloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    s->head |-> head &*&
    stack_contents(head);

#[predicate]
fn stack_contents(head: *mut Node) =
    head == std::ptr::null_mut() ? true : node(head, (*head).next, (*head).value) &*& stack_contents((*head).next);

impl Stack {
    #[requires(true)]
    #[ensures(
        result != std::ptr::null_mut() && 
        stack(result, std::ptr::null_mut())
    )]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(
        stack != std::ptr::null_mut() &&
        stack(stack, head)
    )]
    #[ensures(
        stack(stack, new_head) &*&
        node(n, head, value)
    )]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(
        stack != std::ptr::null_mut() &&
        stack(stack, head) &&
        head != std::ptr::null_mut() &&
        node(head, next, val)
    )]
    #[ensures(
        result == val &&
        stack(stack, next)
    )]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(
        stack != std::ptr::null_mut() &&
        stack(stack, head)
    )]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        // loop to deallocate all nodes
        let mut cur = (*stack).head;
        while cur != std::ptr::null_mut()
            invariant stack_contents(cur)
        {
            let next = (*cur).next;
            dealloc(cur as *mut u8, Layout::new::<Node>());
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