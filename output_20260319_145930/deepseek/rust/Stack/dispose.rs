use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred node(n: *mut Node, next: *mut Node, value: i32) =
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
pred stack(s: *mut Stack, head: *mut Node) =
    alloc_block(s, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> head;
@*/

struct Stack {
    head: *mut Node,
}

/*@
pred nodes(n: *mut Node) =
    n == std::ptr::null_mut() ?
        true
    :
        node(n, next, value) &*& nodes(next);
@*/

//@ req nodes(n);
//@ ens true;
unsafe fn dispose_nodes(n: *mut Node)
{
    //@ open nodes(n);
    if !n.is_null() {
        //@ open node(n, _, _);
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    //@ req true;
    //@ ens stack(result, std::ptr::null_mut());
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, std::ptr::null_mut());
        return stack;
    }
    
    //@ req stack(stack, head);
    //@ ens stack(stack, head) &*& result == head.is_null();
    unsafe fn is_empty(stack: *mut Stack) -> bool
    {
        //@ open stack(stack, head);
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        //@ close stack(stack, head);
        return result;
    }

    //@ req stack(stack, head);
    //@ ens stack(stack, n) &*& node(n, head, value);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack, head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, head, value);
        //@ close stack(stack, n);
    }

    //@ req stack(stack, head) &*& head != std::ptr::null_mut() &*& node(head, next, value);
    //@ ens stack(stack, next) &*& result == value;
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack, head);
        let head = (*stack).head;
        //@ open node(head, next, value);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, next);
        return result;
    }
    
    //@ req stack(stack, head);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack, head);
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
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}