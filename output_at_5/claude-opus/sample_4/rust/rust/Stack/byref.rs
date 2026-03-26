use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

// verifast_options{}

//@ predicate node(*mut Node n; i32 value, *mut Node next) =
//@     n->value |-> value &*& n->next |-> next;

//@ predicate nodes(*mut Node n) =
//@     n == std::ptr::null_mut() ? true :
//@         (node(n, ?v, ?nx) &*& nodes(nx));

//@ predicate stack(*mut Stack s; *mut Node head) =
//@     s->head |-> head &*& nodes(head);

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    //@ requires true;
    //@ ensures true;
{
    if !(*n).is_null() {
        //@ open nodes(*n);
        let keep = p((**n).value);
        if keep {
            //@ open node(*n, _, _);
            filter_nodes(&raw mut (**n).next, p);
            //@ close node(*n, (**n).value, (**n).next);
        } else {
            let next_ = (**n).next;
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
            //@ return;
        }
        //@ close nodes(*n);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    //@ requires true;
    //@ ensures true;
{
    if !n.is_null() {
        //@ open nodes(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
        //@ requires true;
        //@ ensures true;
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, std::ptr::null_mut());
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
        //@ requires true;
        //@ ensures true;
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //* updated stack head *//
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        //@ requires true;
        //@ ensures true;
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
        //@ requires true;
        //@ ensures true;
    {
        filter_nodes(&raw mut (*stack).head, p);
    }
    
    unsafe fn dispose(stack: *mut Stack)
        //@ requires true;
        //@ ensures true;
    {
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

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}