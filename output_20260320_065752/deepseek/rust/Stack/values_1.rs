use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}
/*@
pred Node(node: *mut Node; next: *mut Node, value: i32) =
    alloc_block(node, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(node) &*&
    (*node).next |-> next &*&
    (*node).value |-> value;
@*/

struct Stack {
    head: *mut Node,
}
/*@
pred Stack(stack: *mut Stack; head: *mut Node) =
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> head;
@*/

/*@
pred lseg(start: *mut Node, end: *mut Node) =
    start == end ?
        true
    :
        Node(start, next, _) &*& lseg(next, end);
@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack(result, std::ptr::null_mut());
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Stack(stack, std::ptr::null_mut());
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack(stack, head);
    //@ ens Stack(stack, ?new_head) &*& Node(new_head, head, value);
    {
        //@ open Stack(stack, head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Node(n, (*stack).head, value);
        (*stack).head = n;
        //@ close Stack(stack, n);
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack, std::ptr::null_mut());
    //@ ens true;
    {
        //@ open Stack(stack, std::ptr::null_mut());
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}