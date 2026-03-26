use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ pred node(n: *mut Node; next: *mut Node, value: i32) =
    n != 0 &*& struct_Node_padding(n) &*&
    (*n).next |-> next &*& (*n).value |-> value;
@*/

/*@ pred stack(s: *mut Stack; head: *mut Node) =
    s != 0 &*& struct_Stack_padding(s) &*&
    (*s).head |-> head;
@*/

/*@ pred nodes(head: *mut Node; values: list<i32>) =
    match values {
        nil => head == 0,
        cons(v, vs) => head != 0 &*& node(head, ?next, v) &*& nodes(next, vs)
    };
@*/

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

//@ req stack(stack, ?old_head) &*& nodes(old_head, ?vs);
//@ ens stack(stack, ?new_head) &*& nodes(new_head, cons(value, vs));
unsafe fn push(stack: *mut Stack, value: i32)
{
//@ open stack(stack, old_head);
let n = alloc(Layout::new::<Node>()) as *mut Node;
if n.is_null() {
handle_alloc_error(Layout::new::<Node>());
}
//@ close node(n, old_head, value);
(*n).next = (*stack).head;
(*n).value = value;
(*stack).head = n;
//@ close stack(stack, n);
}

//@ req stack(stack, ?head) &*& nodes(head, _);
//@ ens true;
unsafe fn dispose(stack: *mut Stack)
{
//@ open stack(stack, _);
dealloc(stack as *mut u8, Layout::new::<Stack>());
}
}