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
//@ ens stack(result) &*& (*result).head |-> ?h &*& h == null;
{
let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
if stack.is_null() {
handle_alloc_error(Layout::new::<Stack>());
}
(*stack).head = std::ptr::null_mut();
//@ close stack(stack);
stack
}
unsafe fn push(stack: *mut Stack, value: i32)
//@ req stack(stack) &*& (*stack).head |-> ?old_head;
//@ ens stack(stack) &*& (*stack).head |-> ?new_head &*& new_head != null &*& node(new_head, old_head, value);
{

let n = alloc(Layout::new::<Node>()) as *mut Node;
if n.is_null() {
handle_alloc_error(Layout::new::<Node>());
}
(*n).next = (*stack).head;
(*n).value = value;
//@ close node(n, (*stack).head, value);
(*stack).head = n;
//@ open stack(stack);
//@ close stack(stack);

}
unsafe fn dispose(stack: *mut Stack)
//@ req stack(stack);
//@ ens true;
{

dealloc(stack as *mut u8, Layout::new::<Stack>());
}
}

//@ pred node(n: *mut Node, next: *mut Node, value: i32) =
//@   n != null &*& struct_Node_padding(n) &*& (*n).next |-> next &*& (*n).value |-> value;

//@ pred stack(s: *mut Stack) =
//@   s != null &*& struct_Stack_padding(s) &*& (*s).head |-> ?h &*& nodes(h);

//@ fixpoint bool nodes(*mut Node head); // abstract list predicate

//@ lemma_auto(nodes_nil) () : nodes(null);
//@ ensures true;
//@ { }

//@ lemma_auto(nodes_cons) (n: *mut Node, next: *mut Node, v: i32) :
//@   node(n, next, v) &*& nodes(next) ==>
//@   nodes(n);
//@ ensures true;
//@ { }