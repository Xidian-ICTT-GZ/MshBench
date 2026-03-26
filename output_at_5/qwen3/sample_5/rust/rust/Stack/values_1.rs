use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
next: *mut Node,
value: i32,
}
struct Stack {
head: *mut Node,
}

//@ ghost predicate stack_valid(s: *mut Stack) = s != null() ==> owns_stack_content(s);
//@ ghost predicate owns_stack_content(s: *mut Stack) = owned_ptr(s, size_of::<Stack>()) && ((*s).head == null() || (exists n: *mut Node; node_valid(n) && (*s).head == n && list_nodes((*s).head)));
//@ ghost predicate list_nodes(h: *mut Node) = h == null() || (node_valid(h) && list_nodes((*h).next));
//@ ghost predicate node_valid(n: *mut Node) = owned_ptr(n, size_of::<Node>()) && ((*n).next == null() || node_valid((*n).next));

impl Stack {
unsafe fn create() -> *mut Stack
//@ req true;
//@ ens result != null() && stack_valid(result);
{
let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
if stack.is_null() {
handle_alloc_error(Layout::new::<Stack>());
}
(*stack).head = std::ptr::null_mut();
stack
}
unsafe fn push(stack: *mut Stack, value: i32)
//@ req stack_valid(stack);
//@ ens stack_valid(stack);
{
let n = alloc(Layout::new::<Node>()) as *mut Node;
if n.is_null() {
handle_alloc_error(Layout::new::<Node>());
}
open owns_stack_content(stack);
(*n).next = (*stack).head;
(*n).value = value;
(*stack).head = n;
close owns_stack_content(stack);
}
unsafe fn dispose(stack: *mut Stack)
//@ req stack_valid(stack);
//@ ens true;
{
open owns_stack_content(stack);
dealloc(stack as *mut u8, Layout::new::<Stack>());
}
}