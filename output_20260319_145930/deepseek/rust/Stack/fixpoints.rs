use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred node(n: *mut Node; next: *mut Node, value: i32) =
    alloc_block(n, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;
@*/

/*@
pred nodes(n: *mut Node) =
    n == std::ptr::null_mut() ?
        true
    :
        node(n, ?next, ?value) &*& nodes(next);
@*/

/*@
pred stack(s: *mut Stack) =
    alloc_block(s, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> ?head &*&
    nodes(head);
@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result);
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
    //@ req stack(stack) &*& value == value;
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n, (*stack).head, value);
        //@ open nodes((*stack).head);
        //@ close nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == result;
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        //@ open node(head, ?next, ?value);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close nodes(next);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        result
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

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);
        //@ assert result1 == 20;
        let result2 = Stack::pop(s);
        //@ assert result2 == 10;
        Stack::dispose(s);
    }
}