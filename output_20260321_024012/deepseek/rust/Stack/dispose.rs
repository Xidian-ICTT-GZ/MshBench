use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ predicate node(n: *mut Node; next: *mut Node, value: i32) = 
//@     struct_Node_padding(n) &*& (*n).next |-> next &*& (*n).value |-> value;

//@ predicate nodes(n: *mut Node) =
//@     n == 0 ? true : node(n, ?next, _) &*& nodes(next);

//@ predicate stack(s: *mut Stack; head: *mut Node) =
//@     struct_Stack_padding(s) &*& (*s).head |-> head &*& nodes(head);

unsafe fn dispose_nodes(n: *mut Node)
//@ req nodes(n);
//@ ens true;
{
    if !n.is_null() {
        //@ open nodes(n);
        //@ open node(n, _, _);
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(0);
        //@ close stack(stack, 0);
        return stack;
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req stack(stack, ?head);
    //@ ens stack(stack, head) &*& result == (head == 0);
    {
        //@ open stack(stack, head);
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        //@ close stack(stack, head);
        return result;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?head);
    //@ ens stack(stack, ?new_head) &*& node(new_head, head, value);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open stack(stack, head);
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n, head, value);
        //@ close nodes(n);
        (*stack).head = n;
        //@ close stack(stack, n);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, ?head) &*& head != 0;
    //@ ens stack(stack, ?next) &*& node(head, next, result);
    {
        //@ open stack(stack, head);
        //@ open nodes(head);
        //@ open node(head, ?next, ?v);
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, next);
        return result;
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, _);
    //@ ens true;
    {
        //@ open stack(stack, ?head);
        dispose_nodes(head);
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
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}