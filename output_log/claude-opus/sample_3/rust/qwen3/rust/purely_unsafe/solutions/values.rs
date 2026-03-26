use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[predicate]
fn node_pred(node: *mut Node, next: *mut Node, value: i32) =
    node != std::ptr::null_mut() &*&
    node->next |-> next &*&
    node->value |-> value;

#[predicate]
fn stack_pred(stack: *mut Stack, head: *mut Node) =
    stack != std::ptr::null_mut() &*&
    stack->head |-> head;

// Lemmas for splitting and merging fractional permissions or duplications

#[lemma]
fn node_pred_split(node: *mut Node, next: *mut Node, value: i32)
    requires node_pred(node, next, value);
    ensures node_pred(node, next, value) &*& node_pred(node, next, value);
{
    open node_pred(node, next, value);
    close node_pred(node, next, value);
    close node_pred(node, next, value);
}

#[lemma]
fn node_pred_merge(node: *mut Node, next: *mut Node, value: i32)
    requires node_pred(node, next, value) &*& node_pred(node, next, value);
    ensures node_pred(node, next, value);
{
    open node_pred(node, next, value);
    open node_pred(node, next, value);
    close node_pred(node, next, value);
}

#[lemma]
fn stack_pred_split(stack: *mut Stack, head: *mut Node)
    requires stack_pred(stack, head);
    ensures stack_pred(stack, head) &*& stack_pred(stack, head);
{
    open stack_pred(stack, head);
    close stack_pred(stack, head);
    close stack_pred(stack, head);
}

#[lemma]
fn stack_pred_merge(stack: *mut Stack, head: *mut Node)
    requires stack_pred(stack, head) &*& stack_pred(stack, head);
    ensures stack_pred(stack, head);
{
    open stack_pred(stack, head);
    open stack_pred(stack, head);
    close stack_pred(stack, head);
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
        stack_pred(result, std::ptr::null_mut())
    )]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close stack_pred(stack, std::ptr::null_mut());
        stack
    }

    #[requires(
        stack != std::ptr::null_mut() &&
        stack_pred(stack, old_head)
    )]
    #[ensures(
        stack_pred(stack, n) &*&
        node_pred(n, old_head, value)
    )]
    unsafe fn push(stack: *mut Stack, value: i32) {
        open stack_pred(stack, old_head);
        let old_head = (*stack).head;
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = old_head;
        (*n).value = value;
        close node_pred(n, old_head, value);
        (*stack).head = n;
        close stack_pred(stack, n);
    }

    #[requires(
        stack != std::ptr::null_mut() &&
        stack_pred(stack, head)
    )]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        open stack_pred(stack, head);
        let mut current = head;
        while current != std::ptr::null_mut()
            invariant
                current != std::ptr::null_mut() ?
                exists<nxt: *mut Node, val: i32>(node_pred(current, nxt, val)) :
                true
        {
            open node_pred(current, (*current).next, (*current).value);
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