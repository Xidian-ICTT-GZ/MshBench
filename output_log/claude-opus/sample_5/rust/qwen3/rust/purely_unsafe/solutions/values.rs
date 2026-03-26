use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred]
unsafe fn node_pred(node: *mut Node) : 
    node != std::ptr::null_mut() &*& 
    malloc_block_node(node) &*&
    (*node).next |-> ?next &*&
    (*node).value |-> ?value &*&
    (next == std::ptr::null_mut() ? true : node_pred(next))
{}

#[pred]
unsafe fn stack_pred(stack: *mut Stack) : 
    stack != std::ptr::null_mut() &*& 
    malloc_block_stack(stack) &*&
    (*stack).head |-> ?head &*&
    (head == std::ptr::null_mut() ? true : node_pred(head))
{}

#[lemma]
fn node_pred_split(node: *mut Node)
    requires node != std::ptr::null_mut() &*& node_pred(node);
    ensures node_pred(node) &*& node_pred(node);
{
    open node_pred(node);
    if ((*node).next != std::ptr::null_mut()) {
        node_pred_split((*node).next);
    }
    close node_pred(node);
}

#[lemma]
fn node_pred_merge(node: *mut Node)
    requires node != std::ptr::null_mut() &*& node_pred(node) &*& node_pred(node);
    ensures node_pred(node);
{
    open node_pred(node);
    if ((*node).next != std::ptr::null_mut()) {
        node_pred_merge((*node).next);
    }
    close node_pred(node);
}

#[lemma]
fn stack_pred_split(stack: *mut Stack)
    requires stack != std::ptr::null_mut() &*& stack_pred(stack);
    ensures stack_pred(stack) &*& stack_pred(stack);
{
    open stack_pred(stack);
    if ((*stack).head != std::ptr::null_mut()) {
        node_pred_split((*stack).head);
    }
    close stack_pred(stack);
}

#[lemma]
fn stack_pred_merge(stack: *mut Stack)
    requires stack != std::ptr::null_mut() &*& stack_pred(stack) &*& stack_pred(stack);
    ensures stack_pred(stack);
{
    open stack_pred(stack);
    if ((*stack).head != std::ptr::null_mut()) {
        node_pred_merge((*stack).head);
    }
    close stack_pred(stack);
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
        stack_pred(result) &&
        (*result).head == std::ptr::null_mut()
    )]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        close stack_pred(stack);
        stack
    }

    #[requires(
        stack != std::ptr::null_mut() &&
        stack_pred(stack)
    )]
    #[ensures(
        stack_pred(stack) &&
        node_pred((*stack).head) &&
        (*(*stack).head).value == value
    )]
    unsafe fn push(stack: *mut Stack, value: i32) {
        open stack_pred(stack);
        let old_head = (*stack).head;
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = old_head;
        (*n).value = value;
        close node_pred(n);
        (*stack).head = n;
        close stack_pred(stack);
    }

    #[requires(
        stack != std::ptr::null_mut() &&
        stack_pred(stack)
    )]
    #[ensures(
        emp
    )]
    unsafe fn dispose(stack: *mut Stack) {
        open stack_pred(stack);
        let mut current = (*stack).head;
        close stack_pred(stack); // to keep invariant on stack pointer during loop
        while current != std::ptr::null_mut() {
            open node_pred(current);
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