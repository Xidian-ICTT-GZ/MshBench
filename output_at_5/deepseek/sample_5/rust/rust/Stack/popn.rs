use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ predicate node(n: *mut Node; next: *mut Node, value: i32) =
//@     alloc_block(n, std::mem::size_of::<Node>()) &*&
//@     struct_Node_padding(n) &*&
//@     (*n).next |-> next &*&
//@     (*n).value |-> value;

//@ predicate nodes(n: *mut Node) =
//@     n == 0 ? true : node(n, ?next, _) &*& nodes(next);

//@ predicate stack(s: *mut Stack) =
//@     alloc_block(s, std::mem::size_of::<Stack>()) &*&
//@     struct_Stack_padding(s) &*&
//@     (*s).head |-> ?head &*&
//@     nodes(head);

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes(nodes);
//@ ens nodes(nodes);
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open nodes(nodes);
        //@ open node(nodes, ?next, ?val);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close node(nodes, next, val);
        //@ close nodes(nodes);
    }
    
    result
}

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
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        let result = (*stack).head.is_null();
        //@ close nodes(head);
        //@ close stack(stack);
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack);
        result
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
        //@ close node(n, (*stack).head, value);
        //@ close nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        //@ open node(head, ?next, ?val);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        result
    }
    
    unsafe fn popn(stack: *mut Stack, n: i32)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        let mut i = 0;
        loop {
            //@ invariant stack(stack) &*& 0 <= i &*& i <= n;
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        let mut n = (*stack).head;
        loop {
            //@ invariant nodes(n);
            if n.is_null() {
                break;
            }
            //@ open nodes(n);
            //@ open node(n, ?next, _);
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        //@ open nodes(std::ptr::null_mut());
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