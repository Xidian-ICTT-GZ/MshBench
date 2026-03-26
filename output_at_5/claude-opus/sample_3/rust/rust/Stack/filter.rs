use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred nodes_pred(*mut Node n, list<int> ns) =  
//@     n == std::ptr::null_mut() ? ns == nil :
//@     exists<int v, *mut Node next>(
//@         n != std::ptr::null_mut() &*&
//@         n->value |-> v &*&
//@         n->next |-> next &*&
//@         nodes_pred(next, ?ns0) &*&
//@         ns == cons(v, ns0)
//@     );
//
//@ predicate stack(stack_ptr: *mut Stack, nodes: list<int>) = 
//@     stack_ptr != std::ptr::null_mut() &*& 
//@     stack_ptr->head |-> ?head &*&
//@     nodes_pred(head, nodes);

type I32Predicate = unsafe fn(i32) -> bool;

//@ requires nodes_pred(n, ?ns);
//@ ensures nodes_pred(result, ?ns2);
unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);
            //@ open nodes_pred(n, ns);
            //@ assert n->value |-> ?v &*& n->next |-> ?nx &*& nodes_pred(nx, ?ns0) &*& ns == cons(v, ns0);
            (*n).next = next;
            //@ close nodes_pred(n, cons((*n).value, _));
            n
        } else {
            next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
    }
}

//@ requires nodes_pred(n, ?ns);
//@ ensures nodes_pred(nil, nil);
unsafe fn dispose_nodes(n: *mut Node)
{
    if !n.is_null() {
        //@ open nodes_pred(n, _);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    //@ requires true;
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
    
    //@ requires stack(stack, ?ns);
    //@ ensures stack(stack, cons(value, ns));
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

    //@ requires stack(stack, cons(?v, ?ns));
    //@ ensures stack(stack, ns);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }
    
    //@ requires stack(stack, ?ns);
    //@ ensures stack(stack, _);
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    {
        let head = filter_nodes((*stack).head, p);
        (*stack).head = head;
    }
    
    //@ requires stack(stack, ?ns);
    //@ ensures true;
    unsafe fn dispose(stack: *mut Stack)
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

//@ requires true;
//@ ensures true;
unsafe fn neq_20(x: i32) -> bool
{
    x != 20
}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}