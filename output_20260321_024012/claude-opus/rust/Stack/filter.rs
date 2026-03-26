use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

//@ pred node<n>(p: *mut Node) = p |-> Node { next: ?next, value: ?v } &*& node<n>(next) &*& n == n;

struct Stack {
    head: *mut Node,
}

//@ pred stack(s: *mut Stack) = s |-> Stack { head: ?head } &*& node(head);

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
//@ requires [?f]node(n) &*& p(_, _) == true;
//@ ensures node(result);
{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        //@ open node(n);
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);
            (*n).next = next;
            //@ close node(n);
            n
        } else {
            next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            //@ close node(std::ptr::null_mut());
            let result = filter_nodes(next, p);
            result
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ requires node(n);
//@ ensures true;
{
    if !n.is_null() {
        //@ open node(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
        //@ close node(std::ptr::null_mut());
    }
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
        //@ close node(std::ptr::null_mut());
        //@ close stack(stack);
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack);
    //@ ensures stack(stack);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open stack(stack);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n);
        //@ close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack) &*& (*stack).head != std::ptr::null_mut();
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
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ requires stack(stack);
    //@ ensures stack(stack);
    {
        //@ open stack(stack);
        let head = filter_nodes((*stack).head, p);
        (*stack).head = head;
        //@ close stack(stack);
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack);
    //@ ensures true;
    {
        //@ open stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool
//@ requires true;
//@ ensures true;
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