use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[predicate]
fn NodesList(mut current: *mut Node) =
    current == std::ptr::null_mut() ?
        emp
    :
        current |-> Node { next: ?next, value: _ } &*& NodesList(next);

#[predicate]
fn StackPred(head: *mut Node, stack: *mut Stack) =
    stack != std::ptr::null_mut() &*&
    stack |-> Stack { head: head } &*& NodesList(head);

#[predicate]
fn NodePred(node: *mut Node, next: *mut Node, value: i32) =
    node != std::ptr::null_mut() &*&
    node |-> Node { next: next, value: value };

#[lemma]
fn node_pred_split(node: *mut Node, next: *mut Node, value: i32)
    requires
        NodePred(node, next, value);
    ensures
        NodePred(node, next, value) &*&
        NodePred(node, next, value);
{
    open NodePred(node, next, value);
    close NodePred(node, next, value);
    close NodePred(node, next, value);
}

#[lemma]
fn node_pred_merge(node: *mut Node, next: *mut Node, value: i32)
    requires
        NodePred(node, next, value) &*&
        NodePred(node, next, value);
    ensures
        NodePred(node, next, value);
{
    open NodePred(node, next, value);
    open NodePred(node, next, value);
    close NodePred(node, next, value);
}

#[lemma]
fn stack_pred_split(stack: *mut Stack, head: *mut Node)
    requires
        StackPred(head, stack);
    ensures
        StackPred(head, stack) &*&
        StackPred(head, stack);
{
    open StackPred(head, stack);
    close StackPred(head, stack);
    close StackPred(head, stack);
}

#[lemma]
fn stack_pred_merge(stack: *mut Stack, head: *mut Node)
    requires
        StackPred(head, stack) &*&
        StackPred(head, stack);
    ensures
        StackPred(head, stack);
{
    open StackPred(head, stack);
    open StackPred(head, stack);
    close StackPred(head, stack);
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
        StackPred(std::ptr::null_mut(), result)
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
        StackPred(old_head, stack)
    )]
    #[ensures(
        StackPred(n, stack) &*&
        NodePred(n, old_head, value)
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
        StackPred(head, stack)
    )]
    #[ensures(
        emp
    )]
    unsafe fn dispose(stack: *mut Stack) {
        let head = (*stack).head;
        let mut current = head;
        #[invariant(
            current: *mut Node,
            NodesList(current) &*& stack |-> Stack { head: head }
        )]
        while current != std::ptr::null_mut() {
            let next = (*current).next;
            open NodesList(current);
            open NodePred(current, next, _);
            dealloc(current as *mut u8, Layout::new::<Node>());
            current = next;
        }
        close NodesList(std::ptr::null_mut());
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}