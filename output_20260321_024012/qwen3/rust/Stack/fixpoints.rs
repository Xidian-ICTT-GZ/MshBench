use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred node(node: *mut Node; next: *mut Node, value: i32) = (*node).next |-> next &*& (*node).value |-> value;
//@ pred stack(stack: *mut Stack; nodes: list<*mut Node>) =
//@   match nodes with
//@   | nil => (*stack).head |-> null
//@   | cons(h, t) => (*stack).head |-> h &*& node(h, ?next, ?val) &*& stack_nodes(next, t)
//@ ;
//@ fix stack_nodes(head: *mut Node, nodes: list<*mut Node>) =
//@   match nodes with
//@   | nil => head == null
//@   | cons(h, t) => h == head &*& node(h, ?next, ?val) &*& stack_nodes(next, t)
//@ ;

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close stack(stack, nil);
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?nodes);
    //@ ens stack(stack, cons(?n, nodes));
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open stack(stack, nodes);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, (*n).next, value);
        //@ close stack(stack, cons(n, nodes));
        
        
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, cons(?n, ?nodes));
    //@ ens stack(stack, nodes) &*& result == ?val;
    {
        
        let head = (*stack).head;
        //@ open stack(stack, cons(n, nodes));
        //@ open node(head, ?next, val);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, nodes);
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, nil);
    //@ ens true;
    {
        //@ open stack(stack, nil);
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