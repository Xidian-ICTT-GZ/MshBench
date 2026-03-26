use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
next: *mut Node,
value: i32,
}
struct Stack {
head: *mut Node,
}

/*@

pred node(p: *mut Node) =
    (*p).next |-> ?nxt &*& (*p).value |-> ?v;

pred nodes(p: *mut Node) =
    if p == std::ptr::null_mut() {
        true
    } else {
        node(p) &*& nodes((*p).next)
    };

pred stack(s: *mut Stack) =
    (*s).head |-> ?h &*& nodes(h);

@*/

impl Stack {
unsafe fn create() -> *mut Stack
//@ req true;
//@ ens result != std::ptr::null_mut() &*& stack(result);
{
let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
if stack.is_null() {
handle_alloc_error(Layout::new::<Stack>());
}
(*stack).head = std::ptr::null_mut();
//@ close nodes(std::ptr::null_mut());
//@ close stack(stack);

stack
}
unsafe fn push(stack: *mut Stack, value: i32)
//@ req stack(stack);
//@ ens stack(stack);
{

//@ open stack(stack);
//@ assert (*stack).head |-> ?h0 &*& nodes(h0);
let n = alloc(Layout::new::<Node>()) as *mut Node;
if n.is_null() {
handle_alloc_error(Layout::new::<Node>());
}
(*n).next = (*stack).head;
(*n).value = value;
//@ close node(n);
//@ close nodes(n);
(*stack).head = n;
//@ close stack(stack);

}
unsafe fn dispose(stack: *mut Stack)
//@ req stack(stack);
//@ ens true;
{

//@ open stack(stack);
//@ open nodes((*stack).head);
dealloc(stack as *mut u8, Layout::new::<Stack>());
}
}