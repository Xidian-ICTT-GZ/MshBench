use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

//@ pred node(n: *mut Node) =
//@     malloc_block(n, sizeof<Node>()) &*&
//@     n->next |-> ?next &*& n->value |-> _ &*& (next == std::ptr::null_mut() ? true : node(next));

struct Stack {
    head: *mut Node,
}

//@ pred stack(s: *mut Stack) =
//@     malloc_block(s, sizeof<Stack>()) &*& s->head |-> ?head &*& (head == std::ptr::null_mut() ? true : node(head));

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ requires nodes == std::ptr::null_mut() || node(nodes);
//@ ensures true;
{
    let mut result = 0;
    if !nodes.is_null() {
        //@ open node(nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close node(nodes);
    }
    result
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack);
        stack
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ requires stack(stack);
    //@ ensures stack(stack);
    {
        //@ open stack(stack);
        let result = (*stack).head.is_null();
        //@ close stack(stack);
        result
    }

    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ requires stack(stack);
    //@ ensures stack(stack);
    {
        //@ open stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack);
    //@ ensures stack(stack);
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n);
        //@ close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack) &*& (*stack).head != std::ptr::null_mut() &*& node((*stack).head);
    //@ ensures stack(stack);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open node(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack);
    //@ ensures true;
    {
        //@ open stack(stack);
        let mut n = (*stack).head;
        while !n.is_null()
        //@ invariant n == std::ptr::null_mut() || node(n);
        {
            //@ open node(n);
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}