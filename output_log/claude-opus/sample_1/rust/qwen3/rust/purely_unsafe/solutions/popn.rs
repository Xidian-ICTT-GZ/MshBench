use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::ptr::null_mut;

#[repr(C)]
pub struct Node {
    next: *mut Node,
    value: i32,
}

predicate node_pred(node: *mut Node;) =
    node != null_mut() &*&
    // own allocation of the Node struct at 'node'
    malloc_block_node(node) &*&
    // points-to fields
    *node.next |-> ?next &*&
    *node.value |-> ?value &*&
    // recursively node_pred for next if not null
    (next == null_mut() ? emp : node_pred(next));

predicate malloc_block_node(node: *mut Node;) = true; 
// Assume Rust allocator yields malloc_block for Node (size_of Node)

predicate stack_pred(stack: *mut Stack;) =
    stack != null_mut() &*&
    malloc_block_stack(stack) &*&
    *stack.head |-> ?head &*& list_pred(head);

predicate malloc_block_stack(stack: *mut Stack;) = true; 
// Assume Rust allocator yields malloc_block for Stack

predicate list_pred(head: *mut Node;) =
    (head == null_mut() ? emp : node_pred(head));

#[repr(C)]
pub struct Stack {
    head: *mut Node,
}

#[requires(true)]
#[ensures(result != null_mut())]
fn alloc_node(value: i32) -> *mut Node
    // Allocates a node with given value and next = null
    // Returns owned pointer and node_pred predicate
    //@ requires emp;
    //@ ensures node_pred(result);
{
    let layout = Layout::new::<Node>();
    let node_ptr = unsafe { alloc(layout) } as *mut Node;
    if node_ptr.is_null() {
        unsafe { handle_alloc_error(layout); }
    }
    unsafe {
        (*node_ptr).next = null_mut();
        (*node_ptr).value = value;
    }
    //@ close malloc_block_node(node_ptr);
    //@ close node_pred(node_ptr);
    node_ptr
}

#[requires(node_pred(node))]
#[ensures(emp)]
fn dealloc_node(node: *mut Node)
    //@ requires node_pred(node);
    //@ ensures emp;
{
    if node != null_mut() {
        let next = unsafe { (*node).next };
        if next != null_mut() {
            dealloc_node(next);
        }
        let layout = Layout::new::<Node>();
        //@ open node_pred(node);
        //@ open malloc_block_node(node);
        unsafe { dealloc(node as *mut u8, layout) };
    }
}

#[requires(emp)]
#[ensures(stack_pred(result))]
fn alloc_stack() -> *mut Stack
    //@ requires emp;
    //@ ensures stack_pred(result);
{
    let layout = Layout::new::<Stack>();
    let stack_ptr = unsafe { alloc(layout) } as *mut Stack;
    if stack_ptr.is_null() {
        unsafe { handle_alloc_error(layout); }
    }
    unsafe {
        (*stack_ptr).head = null_mut();
    }
    //@ close malloc_block_stack(stack_ptr);
    //@ close stack_pred(stack_ptr);
    stack_ptr
}

#[requires(stack_pred(stack))]
#[ensures(emp)]
fn dealloc_stack(stack: *mut Stack)
    //@ requires stack_pred(stack);
    //@ ensures emp;
{
    let head = unsafe { (*stack).head };
    if head != null_mut() {
        dealloc_node(head);
    }
    let layout = Layout::new::<Stack>();
    //@ open stack_pred(stack);
    //@ open malloc_block_stack(stack);
    unsafe { dealloc(stack as *mut u8, layout) };
}

#[requires(stack_pred(stack))]
#[ensures(stack_pred(stack))]
fn push(stack: *mut Stack, value: i32)
    //@ requires stack_pred(stack);
    //@ ensures stack_pred(stack);
{
    let new_node = alloc_node(value);
    let old_head = unsafe { (*stack).head };
    unsafe { (*new_node).next = old_head; }
    unsafe { (*stack).head = new_node; }
}

#[requires(stack_pred(stack))]
#[ensures(stack_pred(stack))]
fn pop(stack: *mut Stack) -> Option<i32>
    //@ requires stack_pred(stack);
    //@ ensures stack_pred(stack);
{
    let head = unsafe { (*stack).head };
    if head == null_mut() {
        None
    } else {
        let value = unsafe { (*head).value };
        let next = unsafe { (*head).next };
        unsafe { (*stack).head = next; }
        dealloc_node(head);
        Some(value)
    }
}