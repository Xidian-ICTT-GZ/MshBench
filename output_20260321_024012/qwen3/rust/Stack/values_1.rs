//@ pred Node(node: *mut Node; next: *mut Node, value: i32) = (*node).next |-> next &*& (*node).value |-> value;
//@ pred Stack(stack: *mut Stack; head: *mut Node) = (*stack).head |-> head;

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
next: *mut Node,
value: i32,
}
struct Stack {
head: *mut Node,
}

impl Stack {
unsafe fn create() -> *mut Stack
//@ req true;
//@ ens Stack(result, std::ptr::null_mut());
{
let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
if stack.is_null() {
handle_alloc_error(Layout::new::<Stack>());
}
(*stack).head = std::ptr::null_mut();
//@ close Stack(stack, std::ptr::null_mut());
stack
}
unsafe fn push(stack: *mut Stack, value: i32)
//@ req Stack(stack, ?head);
//@ ens Stack(stack, ?new_head);
{
//@ open Stack(stack, _);
let n = alloc(Layout::new::<Node>()) as *mut Node;
if n.is_null() {
handle_alloc_error(Layout::new::<Node>());
}
(*n).next = (*stack).head;
(*n).value = value;
//@ close Node(n, (*stack).head, value);
(*stack).head = n;
//@ close Stack(stack, n);
}
unsafe fn dispose(stack: *mut Stack)
//@ req Stack(stack, _);
//@ ens true;
{
//@ open Stack(stack, _);
dealloc(stack as *mut u8, Layout::new::<Stack>());
}
}