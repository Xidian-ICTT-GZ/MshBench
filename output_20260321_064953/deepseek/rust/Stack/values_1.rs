use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
next: *mut Node,
value: i32,
}
struct Stack {
head: *mut Node,
}

//@ predicate_ctor node(node: *mut Node, next: *mut Node, value: i32)() = 
//@     struct_Node_padding(node) &*& (*node).next |-> next &*& (*node).value |-> value;

//@ predicate nodes(node: *mut Node) = 
//@     node == std::ptr::null_mut() ? true : 
//@         node(node, ?next, ?value)() &*& nodes(next);

//@ predicate stack(stack: *mut Stack) = 
//@     struct_Stack_padding(stack) &*& (*stack).head |-> ?head &*& nodes(head);

impl Stack {
unsafe fn create() -> *mut Stack
//@ req true;
//@ ens stack(result);
{
let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
if stack.is_null() {
handle_alloc_error(Layout::new::<Stack>());
}
//@ close struct_Stack_padding(stack);
//@ close nodes(std::ptr::null_mut());
//@ close stack(stack);
(*stack).head = std::ptr::null_mut();

stack
}
unsafe fn push(stack: *mut Stack, value: i32)
//@ req stack(stack);
//@ ens stack(stack);
{

let n = alloc(Layout::new::<Node>()) as *mut Node;
if n.is_null() {
handle_alloc_error(Layout::new::<Node>());
}
//@ open stack(stack);
//@ open nodes(?head);
//@ close node(n, head, value)();
//@ close nodes(n);
//@ close stack(stack);
(*n).next = (*stack).head;
(*n).value = value;
(*stack).head = n;

}
unsafe fn dispose(stack: *mut Stack)
//@ req stack(stack);
//@ ens true;
{
//@ open stack(stack);
//@ open nodes(_);
dealloc(stack as *mut u8, Layout::new::<Stack>());
}
}