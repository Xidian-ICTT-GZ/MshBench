use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[predicate]
pub unsafe fn node_list(mut n: *mut Node) -> bool {
    if n == std::ptr::null_mut() {
        true
    } else {
        NodePred { next: (*n).next, value: (*n).value, inv: true } &*&
        node_list((*n).next)
    }
}

#[predicate]
pub unsafe fn NodePred(next: *mut Node, value: i32, inv: bool) = 
    inv == true &*&
    n_points_to_field(next) &*&  // placeholder for ownership of next pointer field
    n_points_to_field_value(value); // placeholder for ownership of value field
    // *Note*: Actually VeriFast needs exact heap ownership predicates.
    // We will encode ownership of fields via points_to.

#[predicate]
pub unsafe fn StackPred(head: *mut Node, inv: bool) =
    inv == true &*&
    stack_head_points_to(head);

#[predicate]
pub unsafe fn n_points_to_field(next: *mut Node) = 
    (*(next as *mut Node)).next |-> next;

#[predicate]
pub unsafe fn n_points_to_field_value(value: i32) = 
    (*(next as *mut Node)).value |-> value;

#[predicate]
pub unsafe fn stack_head_points_to(head: *mut Node) =
    // The head field of Stack points to head
    (*(stack as *mut Stack)).head |-> head;

#[lemma]
fn node_pred_inv(n: *mut Node) -> bool
    requires n != std::ptr::null_mut() &*& NodePred((*n).next, (*n).value, true)
    ensures true
{}

#[lemma]
fn stack_pred_inv(s: *mut Stack) -> bool
    requires s != std::ptr::null_mut() &*& StackPred((*s).head, true)
    ensures true
{}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 
    requires nodes == std::ptr::null_mut() || NodePred((*nodes).next, (*nodes).value, true) &*& node_list(nodes)
    ensures result == if nodes == std::ptr::null_mut() { 0 } else { (*nodes).value + get_nodes_sum((*nodes).next) }
{
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    unsafe fn create() -> *mut Stack 
        requires true
        ensures result != std::ptr::null_mut() &*& StackPred(std::ptr::null_mut(), true)
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
        requires stack != std::ptr::null_mut() &*& StackPred((*stack).head, true)
        ensures result == ((*stack).head == std::ptr::null_mut())
    {
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        result
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires stack != std::ptr::null_mut() &*& StackPred((*stack).head, true) &*& node_list((*stack).head)
        ensures result == get_nodes_sum((*stack).head)
    {
        let result = get_nodes_sum((*stack).head);

        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack != std::ptr::null_mut()
            &*& StackPred((*stack).head, true)
        ensures StackPred((*stack).head, true)
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack != std::ptr::null_mut()
            &*& StackPred((*stack).head, true)
            &*& (*stack).head != std::ptr::null_mut()
            &*& NodePred((*(*stack).head).next, (*(*stack).head).value, true)
            &*& node_list((*stack).head)
        ensures StackPred((*stack).head, true)
            &*& result == (*(*stack).head).value
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack != std::ptr::null_mut() &*& StackPred((*stack).head, true) &*& node_list((*stack).head)
        ensures true
    {
        let mut n = (*stack).head;
        loop {
            invariant
                n == std::ptr::null_mut()
                ? StackPred((*stack).head, true)
                : NodePred((*n).next, (*n).value, true) &*& StackPred((*stack).head, true);

            if n.is_null() {
                break;
            }

            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
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

#[repr(C)]
struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
struct Stack {
    head: *mut Node,
}