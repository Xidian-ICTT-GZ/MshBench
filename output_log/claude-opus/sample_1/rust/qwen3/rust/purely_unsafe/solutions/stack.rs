use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_pred(n: *mut Node, value: i32, next: *mut Node) =
    n != std::ptr::null_mut() &*&
    n->value |-> value &*&
    n->next |-> next;

#[predicate]
fn stack_pred(s: *mut Stack, head: *mut Node) =
    s != std::ptr::null_mut() &*&
    s->head |-> head &*&
    nodes_list(head);

#[predicate]
fn nodes_list(n: *mut Node) =
    n == std::ptr::null_mut() ?
        true
    :
        exists<int v, *mut Node next>(
            node_pred(n, v, next) &*& nodes_list(next)
        );

impl Stack {
    unsafe fn create() -> *mut Stack {
        #[requires(Layout::new::<Stack>().size() > 0)]
        #[ensures(result != std::ptr::null_mut() &*& stack_pred(result, std::ptr::null_mut()))]
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() { handle_alloc_error(Layout::new::<Stack>()); }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32) {
        #[requires(stack_pred(stack, ?old_head))]
        #[ensures(stack_pred(stack, ?new_head) &*&
                 new_head != std::ptr::null_mut() &*&
                 node_pred(new_head, value, old_head))]
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() { handle_alloc_error(Layout::new::<Node>()); }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32 {
        #[requires(stack_pred(stack, ?head) &*& head != std::ptr::null_mut())]
        #[ensures(
            result == (old_value) &*&
            stack_pred(stack, (old_next))
            where
                node_pred(head, old_value, old_next) &*&
                true
        )]
        let head = (*stack).head;
        let result = (*head).value;
        let old_next = (*head).next;
        (*stack).head = old_next;

        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    unsafe fn dispose(stack: *mut Stack) {
        #[requires(stack_pred(stack, std::ptr::null_mut()))]
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