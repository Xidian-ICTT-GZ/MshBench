use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
next: *mut Node,
value: i32,
}
struct Stack {
head: *mut Node,
}

//@ predicate node(struct Node *node; struct Node *next, i32 value) = node != 0 &*& struct_Node_padding(node) &*& (*node).next |-> next &*& (*node).value |-> value &*& malloc_block_Node(node);
//@ predicate nodes(struct Node *node;) = node == 0 ? true : node(node, ?next) &*& nodes(next);
//@ predicate stack(struct Stack *stack;) = stack != 0 &*& struct_Stack_padding(stack) &*& (*stack).head |-> ?head &*& nodes(head) &*& malloc_block_Stack(stack);

impl Stack {
unsafe fn create() -> *mut Stack
//@ req true;
//@ ens stack(result);
{
let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
if stack.is_null() {
handle_alloc_error(Layout::new::<Stack>());
}
//@ close nodes(0);
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
(*n).next = (*stack).head;
(*n).value = value;
//@ close node(n, head, value);
//@ close nodes(n);
//@ close stack(stack);
(*stack).head = n;

}
unsafe fn dispose(stack: *mut Stack)
//@ req stack(stack);
//@ ens true;
{
//@ open stack(stack);
//@ open nodes(?head);
//@ close nodes(head);
//@ leak nodes(_);
dealloc(stack as *mut u8, Layout::new::<Stack>());
}
}