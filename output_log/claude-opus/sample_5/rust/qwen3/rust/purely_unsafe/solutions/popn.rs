use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
pub struct Node {
    pub next: *mut Node,
    pub value: i32,
}

predicate node_pred(n: *mut Node) = n != 0 &*&
    malloc_block_Node(n) &*&
    (n->next |-> ?next &*& n->value |-> ?value &*&
     (next == 0 ? true : node_pred(next)));

predicate stack_pred(head: *mut Node) = node_pred(head);

#[requires(old_head == 0 || node_pred(old_head))]
#[ensures(node_pred(result))]
pub unsafe fn push(old_head: *mut Node, val: i32) -> *mut Node
{
    let layout = Layout::new::<Node>();
    let new_node = alloc(layout) as *mut Node;
    if new_node.is_null() {
        handle_alloc_error(layout);
    }
    // We have malloc_block for new_node now
    // Initialize fields
    (*new_node).value = val;
    (*new_node).next = old_head;
    new_node
}

#[requires(node_pred(head))]
#[ensures(node_pred(result) && old_head != 0 ==> node_pred(head))]
pub unsafe fn pop(head: *mut Node) -> (*mut Node, i32) {
    // Precondition: ownership of node_pred(head)
    let val = (*head).value;
    let next = (*head).next;
    let layout = Layout::new::<Node>();
    dealloc(head as *mut u8, layout);
    (next, val)
}

#[requires(node_pred(head))]
#[ensures(node_pred(head))]
pub unsafe fn free_list(mut head: *mut Node) {
    while head != 0
        invariant node_pred(head)
    {
        let next = (*head).next;
        let layout = Layout::new::<Node>();
        dealloc(head as *mut u8, layout);
        head = next;
    }
}

// The initial empty stack is represented by head == 0 with no heap ownership.

#[allow(dead_code)]
fn example_usage() {
    let mut stack: *mut Node = 0 as *mut Node;
    unsafe {
        stack = push(stack, 10);
        stack = push(stack, 20);
        let (new_head, val) = pop(stack);
        stack = new_head;
        free_list(stack);
    }
}