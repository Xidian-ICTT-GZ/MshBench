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
    node == std::ptr::null_mut() ?
        true
    :
        alloc_block_Node(node) &*& (*node).next |-> ?next &*& (*node).value |-> ?v &*& nodes_list(next);

pred stack(stack: *mut Stack) =
    alloc_block_Stack(stack) &*& (*stack).head |-> ?h &*& nodes_list(h);

@*/

impl Stack {
//@ req true;
//@ ens stack(result);
unsafe fn create() -> *mut Stack

{
let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
if stack.is_null() {
handle_alloc_error(Layout::new::<Stack>());
}
(*stack).head = std::ptr::null_mut();

//@ close nodes_list(std::ptr::null_mut());
//@ close stack(stack);

stack
}
//@ req stack(stack);
//@ ens stack(stack);
unsafe fn push(stack: *mut Stack, value: i32)

{
//@ open stack(stack);

let n = alloc(Layout::new::<Node>()) as *mut Node;
if n.is_null() {
handle_alloc_error(Layout::new::<Node>());
}
(*n).next = (*stack).head;
(*n).value = value;
//@ close nodes_list((*stack).head);
//@ close nodes_list(n);
(*stack).head = n;

//@ close stack(stack);

}
//@ req stack(stack);
//@ ens true;
unsafe fn dispose(stack: *mut Stack)

{
//@ open stack(stack);
//@ open nodes_list((*stack).head);
//@ assume_correct
dealloc(stack as *mut u8, Layout::new::<Stack>());
}
}