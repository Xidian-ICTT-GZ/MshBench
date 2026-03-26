use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::ptr::null_mut;

#[repr(C)]
struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
struct Stack {
    head: *mut Node,
}

#[predicate]
fn node(n: *mut Node, next: *mut Node, value: i32) =
    n != null_mut() &*&
    n->next |-> next &*&
    n->value |-> value;

#[predicate]
fn stack(s: *mut Stack, head: *mut Node) =
    s != null_mut() &*&
    s->head |-> head;

#[predicate]
fn stack_list(head: *mut Node) =
    head == null_mut() ? 
        emp : 
        node(head, ?next, ?value) &*&
        stack_list(next);

impl Stack {
    #[requires(true)]
    #[ensures(result != null_mut() &*& stack(result, null_mut()))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = null_mut();
        stack
    }

    #[requires(stack != null_mut() &*& stack(stack, ?head) &*&
               (head == null_mut() || stack_list(head)))]
    #[ensures(stack(stack, ?newHead) &*& stack_list(newHead) &*& newHead != null_mut() &*&
              node(newHead, oldHead, value) &*& oldHead == head)]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        let oldHead = (*stack).head;
        (*n).next = oldHead;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack != null_mut() &*& stack(stack, ?head) &*& (head == null_mut() || stack_list(head)))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        let mut curr = (*stack).head;
        while curr != null_mut()
            invariant stack(stack, curr) &*& (curr == null_mut() || stack_list(curr));
        {
            let next = (*curr).next;
            dealloc(curr as *mut u8, Layout::new::<Node>());
            curr = next;
        }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}