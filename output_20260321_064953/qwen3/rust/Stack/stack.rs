use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred node(node: *mut Node; next: *mut Node, value: i32) = 
//@   node != 0 &*& struct_Node_padding(node) &*&
//@   (*node).next |-> next &*& (*node).value |-> value;

//@ pred stack(stack: *mut Stack; nodes: list<*mut Node>) =
//@   stack != 0 &*& struct_Stack_padding(stack) &*&
//@   (*stack).head |-> ?head &*&
//@   nodes == match head { 0 => nil, _ => cons(head, _) } &*&
//@   stack_nodes(head, nodes);

//@ pred stack_nodes(curr: *mut Node, nodes: list<*mut Node>) =
//@   match nodes {
//@     nil => curr == 0,
//@     cons(n, rest) => curr == n &*& node(n, ?next, _) &*& stack_nodes(next, rest)
//@   };

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close struct_Stack_padding(stack)();
        (*stack).head = std::ptr::null_mut();
        //@ close stack_nodes(0, nil);
        //@ close stack(stack, nil);
        
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?nodes);
    //@ ens stack(stack, cons(?n, nodes));
    {
        //@ open stack(stack, nodes);
        //@ open stack_nodes(?head, nodes);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close struct_Node_padding(n)();
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, head, value);
        //@ close stack_nodes(n, cons(n, nodes));
        //@ close stack(stack, cons(n, nodes));
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, cons(?n, ?rest));
    //@ ens stack(stack, rest) &*& result == ?v &*& node(n, _, v);
    {
        //@ open stack(stack, cons(n, rest));
        //@ open stack_nodes(n, cons(n, rest));
        //@ open node(n, ?next, ?v);
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack_nodes(next, rest);
        //@ close stack(stack, rest);
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, nil);
    //@ ens true;
    {
        //@ open stack(stack, nil);
        //@ open stack_nodes(0, nil);
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