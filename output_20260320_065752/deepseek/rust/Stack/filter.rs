use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Node(n: *mut Node; next: *mut Node, value: i32) =
    alloc_block(n, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;
@*/

/*@
pred lseg(first: *mut Node, last: *mut Node) =
    if (first == last) {
        true
    } else {
        Node(first, ?next, ?val) &*&
        lseg(next, last)
    };
@*/

/*@
pred Stack(stack: *mut Stack) =
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> ?head &*&
    lseg(head, std::ptr::null_mut());
@*/

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
//@ req lseg(n, std::ptr::null_mut());
//@ ens lseg(result, std::ptr::null_mut());
{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        //@ open lseg(n, std::ptr::null_mut());
        //@ open Node(n, _, _);
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);
            //@ close Node(n, next, (*n).value);
            (*n).next = next;
            //@ close lseg(n, std::ptr::null_mut());
            n
        } else {
            next = (*n).next;
            //@ close Node(n, _, _);
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req lseg(n, std::ptr::null_mut());
//@ ens true;
{
    //@ open lseg(n, std::ptr::null_mut());
    if !n.is_null() {
        //@ open Node(n, _, _);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close lseg(std::ptr::null_mut(), std::ptr::null_mut());
        //@ close Stack(stack);
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack(stack);
    //@ ens Stack(stack);
    {
        //@ open Stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Node(n, (*stack).head, value);
        //@ close lseg(n, std::ptr::null_mut());
        (*stack).head = n;
        //@ close Stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack(stack) &*& (*stack).head |-> ?head &*& head != std::ptr::null_mut() &*& Node(head, ?next, ?value);
    //@ ens Stack(stack) &*& result == value;
    {
        //@ open Stack(stack);
        let head = (*stack).head;
        //@ open lseg(head, std::ptr::null_mut());
        //@ open Node(head, _, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack);
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req Stack(stack);
    //@ ens Stack(stack);
    {
        //@ open Stack(stack);
        let head = filter_nodes((*stack).head, p);
        (*stack).head = head;
        //@ close Stack(stack);
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack);
    //@ ens true;
    {
        //@ open Stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool
//@ req true;
//@ ens result == (x != 20);
{
    x != 20
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}