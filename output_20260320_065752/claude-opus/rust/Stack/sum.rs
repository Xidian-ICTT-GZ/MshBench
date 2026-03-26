use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

/*@

pred node(struct Node* n; int val, struct Node* next) = 
    n != 0 &*&
    n->next |-> next &*& n->value |-> val;

pred nodes(struct Node* n; list<int> vs) =
    switch(vs) {
        case nil: n == 0;
        case cons(h, t): node(n, h, ?next) &*& nodes(next, t);
    };

@*/

struct Stack {
    head: *mut Node,
}

/*@

pred stack(struct Stack* s; list<int> vs) =
    s != 0 &*& s->head |-> ?h &*& nodes(h, vs);

@*/

//@ req true;
//@ ens true;
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ requires nodes(?ns) &*& nodes(ns, ?vs);
//@ ensures nodes(nodes, vs) &*& result == if nodes == 0 then 0 else sum(vs);
{
    let mut result = 0;

    if !nodes.is_null() {
        //@ open node(nodes, ?v, ?next);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close node(nodes, v, next);
    }

    result
}

impl Stack {

    //@ req true;
    //@ ensures stack(result, nil);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    //@ req stack(stack, ?vs);
    //@ ensures stack(stack, vs) &*& result == (vs == nil);
    unsafe fn is_empty(stack: *mut Stack) -> bool
    {
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        result
    }

    //@ req stack(stack, ?vs);
    //@ ensures stack(stack, vs) &*& result == sum(vs);
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        let result = get_nodes_sum((*stack).head);

        result
    }

    //@ req stack(stack, ?vs);
    //@ ensures stack(stack, cons(value, vs));
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    //@ req stack(stack, ?vs) &*& vs != nil;
    //@ ensures stack(stack, tail(vs)) &*& result == head(vs);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    //@ req stack(stack, ?vs);
    //@ ensures true;
    unsafe fn dispose(stack: *mut Stack)
    {
        let mut n = (*stack).head;
        //@ open stack(stack, vs);
        //@ open nodes(n, vs);
        //@ close nodes(n, vs); // We'll close after deallocation steps below.
        //@ close stack(stack, vs);

        loop {
            //@ inv nodes(n, _);
            if n.is_null() {
                break;
            }

            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
            //@ open nodes(next, _);
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