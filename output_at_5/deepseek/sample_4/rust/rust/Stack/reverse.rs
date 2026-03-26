use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ predicate node(n: *mut Node; next: *mut Node, value: i32) = struct_Node_padding(n) &*& (*n).next |-> next &*& (*n).value |-> value;
//@ predicate nodes(n: *mut Node) = n == std::ptr::null_mut() ? true : node(n, ?next, ?value) &*& nodes(next);
//@ predicate stack(s: *mut Stack) = struct_Stack_padding(s) &*& (*s).head |-> ?h &*& nodes(h);

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
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, (*stack).head, value);
        //@ close nodes(n);
        //@ close stack(stack);
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        //@ open node(head, ?next, ?value);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        result
    }
    
    unsafe fn reverse(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close nodes(m);
        //@ open nodes(n);
        loop {
            //@ inv nodes(n) &*& nodes(m);
            if n.is_null() {
                break;
            }
            //@ open nodes(n);
            //@ open node(n, ?next, ?value);
            let next = (*n).next;
            (*n).next = m;
            m = n;
            n = next;
            //@ close node(m, (*m).next, value);
            //@ close nodes(m);
        }
        //@ open nodes(std::ptr::null_mut());
        (*stack).head = m;
        //@ close stack(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        //@ open nodes(_);
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
        let result2 = Stack::pop(s);
        Stack::dispose(s);
    }
}