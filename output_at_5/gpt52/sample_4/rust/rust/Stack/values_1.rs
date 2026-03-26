use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
next: *mut Node,
value: i32,
}
struct Stack {
head: *mut Node,
}

/*@

pred nodes_list(node: *mut Node) =
    node == 0 ?
        true
    :
        (*node).next |-> ?nxt &*& (*node).value |-> ?v &*& alloc_block(node as *mut u8, Layout::new::<Node>()) &*& nodes_list(nxt);

pred stack(stack: *mut Stack) =
    (*stack).head |-> ?h &*& alloc_block(stack as *mut u8, Layout::new::<Stack>()) &*& nodes_list(h);

@*/

impl Stack {
unsafe fn create() -> *mut Stack
//@ req true;
//@ ens result != 0 &*& stack(result);
{
let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
if stack.is_null() {
handle_alloc_error(Layout::new::<Stack>());
}
(*stack).head = std::ptr::null_mut();
//@ close nodes_list(0);
//@ close stack(stack);

stack
}
unsafe fn push(stack: *mut Stack, value: i32)
//@ req stack(stack);
//@ ens stack(stack);
{
//@ open stack(stack);

let n = alloc(Layout::new::<Node>()) as *mut Node;
if n.is_null() {
handle_alloc_error(Layout::new::<Node>());
}
(*n).next = (*stack).head;
(*n).value = value;
//@ close nodes_list(n);
(*stack).head = n;

//@ close stack(stack);
}
unsafe fn dispose(stack: *mut Stack)
//@ req stack(stack);
//@ ens true;
{
//@ open stack(stack);
//@ leak nodes_list(_);

dealloc(stack as *mut u8, Layout::new::<Stack>());
}
}