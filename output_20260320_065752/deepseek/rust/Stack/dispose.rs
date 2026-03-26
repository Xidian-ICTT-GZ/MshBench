use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred Node(n: *mut Node; next: *mut Node, value: i32) =
    alloc_block(n, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;
@*/

struct Node {
    next: *mut Node,
    value: i32,
}

/*@
pred Stack(stack: *mut Stack; head: *mut Node) =
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> head;
@*/

struct Stack {
    head: *mut Node,
}

/*@
pred lseg(start: *mut Node, end: *mut Node) =
    start == end ?
        true
    :
        Node(start, next, _) &*& lseg(next, end);
@*/

//@ req lseg(n, std::ptr::null_mut());
//@ ens true;
unsafe fn dispose_nodes(n: *mut Node)
{
    //@ open lseg(n, std::ptr::null_mut());
    if !n.is_null() {
        //@ open Node(n, _, _);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    //@ req true;
    //@ ens Stack(result, std::ptr::null_mut());
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Stack(stack, std::ptr::null_mut());
        return stack;
    }
    
    //@ req Stack(stack, head);
    //@ ens Stack(stack, head) &*& result == head.is_null();
    unsafe fn is_empty(stack: *mut Stack) -> bool
    {
        //@ open Stack(stack, _);
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        //@ close Stack(stack, head);
        return result;
    }

    //@ req Stack(stack, old_head);
    //@ ens Stack(stack, n) &*& Node(n, old_head, value);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open Stack(stack, _);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Node(n, (*n).next, value);
        //@ close Stack(stack, n);
    }

    //@ req Stack(stack, head) &*& Node(head, next, value) &*& head != std::ptr::null_mut();
    //@ ens Stack(stack, next) &*& result == value;
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open Stack(stack, _);
        let head = (*stack).head;
        //@ open Node(head, _, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack, (*stack).head);
        return result;
    }
    
    //@ req Stack(stack, head);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open Stack(stack, _);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        //@ open Stack(s, _);
        //@ open Node((*s).head, _, _);
        Stack::pop(s);
        //@ open Stack(s, _);
        //@ open Node((*s).head, _, _);
        Stack::pop(s);
        Stack::dispose(s);
    }
}