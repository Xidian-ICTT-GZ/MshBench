use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
struct Node {
    next: *mut Node,
    value: i32,
}

#[predicate]
fn node_pred(n: *mut Node) {
    // Ownership of one Node struct at address n,
    // with a points-to to next field and value field,
    // and a predicate for the next node if non-null.
    n != std::ptr::null_mut() &*&
    n->next |-> ?next &*&
    n->value |-> ?value &*&
    (next == std::ptr::null_mut() ? true : node_pred(next));
}

#[predicate]
fn stack_pred(head: *mut Node) {
    // The stack is represented by its head node pointer.
    // The predicate owns the linked list starting at head.
    node_pred(head) || head == std::ptr::null_mut()
}

#[requires(true)]
#[ensures(stack_pred(result))]
fn stack_new() -> *mut Node {
    let ptr = std::ptr::null_mut();
    ptr
}

#[requires(stack_pred(head))]
#[ensures(stack_pred(result))]
fn push(head: *mut Node, value: i32) -> *mut Node {
    // Allocate a new node and link the old list as next.
    unsafe {
        let layout = Layout::new::<Node>();
        let n = alloc(layout) as *mut Node;
        if n.is_null() {
            handle_alloc_error(layout);
        }
        *n = Node { next: head, value: value };
        n
    }
}

#[requires(stack_pred(head) &*& head != std::ptr::null_mut())]
#[ensures(stack_pred(result))]
fn pop(head: *mut Node) -> *mut Node {
    // Deallocate the head node and return next as new head.
    unsafe {
        let next = (*head).next;
        let layout = Layout::new::<Node>();
        dealloc(head as *mut u8, layout);
        next
    }
}