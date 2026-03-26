use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ pred node(p: *mut Node, next: *mut Node, value: i32) = 
    p != 0 &*& 
    [_]is_Node::<Node>(p) &*& 
    struct_Node_padding(p) &*& 
    (*p).next |-> next &*& 
    (*p).value |-> value;
@*/

/*@ pred stack(p: *mut Stack, head: *mut Node) = 
    p != 0 &*& 
    [_]is_Stack::<Stack>(p) &*& 
    struct_Stack_padding(p) &*& 
    (*p).head |-> head;
@*/

/*@ pred nodes(p: *mut Node) = 
    p == 0 ? true : 
    exists(?next, ?value) &*& node(p, next, value) &*& nodes(next);
@*/

struct Node {
next: *mut Node,
value: i32,
}
struct Stack {
head: *mut Node,
}

impl Stack {
//@ req true;
//@ ens stack(result, 0);
unsafe fn create() -> *mut Stack
{
let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
if stack.is_null() {
handle_alloc_error(Layout::new::<Stack>());
}
//@ close stack(stack, 0);
(*stack).head = std::ptr::null_mut();
stack
}

//@ req stack(stack, ?old_head) &*& nodes(old_head);
//@ ens stack(stack, ?new_head) &*& nodes(new_head);
unsafe fn push(stack: *mut Stack, value: i32)
{
//@ open stack(stack, _);
let n = alloc(Layout::new::<Node>()) as *mut Node;
if n.is_null() {
handle_alloc_error(Layout::new::<Node>());
}
//@ close node(n, (*stack).head, value);
(*n).next = (*stack).head;
(*n).value = value;
(*stack).head = n;
//@ close stack(stack, n);
}

//@ req stack(stack, ?head) &*& nodes(head);
//@ ens true;
unsafe fn dispose(stack: *mut Stack)
{
//@ open stack(stack, _);
dealloc(stack as *mut u8, Layout::new::<Stack>());
}
}