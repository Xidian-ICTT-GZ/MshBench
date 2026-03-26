use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred]
struct NodePred {
    next: *mut Node,
    value: i32,
    #[heap] node: *mut Node,
}

#[pred]
struct StackPred {
    head: *mut Node,
    #[heap] stack: *mut Stack,
}

#[lemma]
fn node_pred_split(node: *mut Node, next: *mut Node, value: i32)
    requires
        node != std::ptr::null_mut(),
        NodePred { next, value, node },
    ensures
        NodePred { next, value, node } &*&
        NodePred { next, value, node },
{
}

#[lemma]
fn node_pred_merge(node: *mut Node, next: *mut Node, value: i32)
    requires
        node != std::ptr::null_mut(),
        NodePred { next, value, node },
        NodePred { next, value, node },
    ensures
        NodePred { next, value, node },
{
}

#[lemma]
fn stack_pred_split(stack: *mut Stack, head: *mut Node)
    requires
        stack != std::ptr::null_mut(),
        StackPred { head, stack },
    ensures
        StackPred { head, stack } &*&
        StackPred { head, stack },
{
}

#[lemma]
fn stack_pred_merge(stack: *mut Stack, head: *mut Node)
    requires
        stack != std::ptr::null_mut(),
        StackPred { head, stack },
        StackPred { head, stack },
    ensures
        StackPred { head, stack },
{
}

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {
    #[requires(
        Layout::new::<Stack>().size() > 0 &&
        Layout::new::<Stack>().align() > 0
    )]
    #[ensures(
        result != std::ptr::null_mut() &&
        StackPred { head: std::ptr::null_mut(), stack: result }
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
        StackPred { head: _, stack }
    )]
    #[ensures(
        stack != std::ptr::null_mut() &&
        StackPred { head: n, stack } &&
        NodePred { next: old_head, value, node: n }
    )]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let old_head = (*stack).head;
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = old_head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(
        stack != std::ptr::null_mut() &&
        StackPred { head: head, stack }
    )]
    #[ensures(
        true
    )]
    unsafe fn dispose(stack: *mut Stack) {
        let head = (*stack).head;
        let mut current = head;
        while current != std::ptr::null_mut() {
            let next = (*current).next;
            dealloc(current as *mut u8, Layout::new::<Node>());
            current = next;
        }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}