use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

#[predicate]
fn node(n: *mut Node) -> bool {
    exists<next: *mut Node, value: i32> n != std::ptr::null_mut() && struct_Node!{n => Node { next, value }} && (next == std::ptr::null_mut() || node(next))
}

#[predicate]
fn nodes(n: *mut Node) -> bool {
    n == std::ptr::null_mut() || node(n)
}

#[predicate]
fn stack(s: *mut Stack) -> bool {
    exists<head: *mut Node> s != std::ptr::null_mut() && struct_Stack!{s => Stack { head }} && nodes(head)
}

#[predicate]
fn predicate_owned(p: I32Predicate) -> bool {
    true
}

#[predicate]
fn predicate_shared(p: I32Predicate) -> bool {
    true
}

#[requires(stack(s))]
#[requires(predicate_owned(p))]
#[ensures(stack(s))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate) {
    if !(*n).is_null() {
        #[invariant(stack_ptr, stack(?s) && struct_Stack!{s => Stack { head: *n }})]
        #[invariant(nodes_rest, nodes(*n))]
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

    #[requires(stack(stack) && (*stack).head != std::ptr::null_mut())]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }
    
    #[requires(stack(stack))]
    #[requires(predicate_owned(p))]
    #[ensures(stack(stack))]
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

#[requires(predicate_shared(neq_20))]
#[ensures(result == (x != 20))]
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