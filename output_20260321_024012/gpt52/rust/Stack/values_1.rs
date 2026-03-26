use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
next: *mut Node,
value: i32,
}
struct Stack {
head: *mut Node,
}

/*@

pred nodes(struct Node *n;) =
    n == 0 ?
        true
    :
        (*n).next |-> ?next &*& (*n).value |-> ?v &*& nodes(next);

pred stack(struct Stack *s;) =
    (*s).head |-> ?h &*& nodes(h);

@*/

impl Stack {
unsafe fn create() -> *mut Stack
//@ req true;
//@ ens result == 0 ? true : stack(result);
{
let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
if stack.is_null() {
handle_alloc_error(Layout::new::<Stack>());
}
(*stack).head = std::ptr::null_mut();
//@ close nodes(0);
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
//@ open nodes(?oldHead);
(*n).next = (*stack).head;
(*n).value = value;
(*stack).head = n;
//@ close nodes(oldHead);
//@ close nodes(n);
//@ close stack(stack);

}
unsafe fn dispose(stack: *mut Stack)
//@ req stack(stack);
//@ ens true;
{

//@ open stack(stack);
//@ open nodes(?h);
dealloc(stack as *mut u8, Layout::new::<Stack>());
}
}