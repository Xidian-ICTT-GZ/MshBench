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
        Node(first, ?next, ?value) &*&
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

//@ req lseg(n, std::ptr::null_mut());
//@ ens lseg(n, std::ptr::null_mut());
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
{
    //@ open lseg(*n, std::ptr::null_mut());
    if !(*n).is_null() {
        //@ open Node(*n, ?next, ?value);
        let keep = p((**n).value);
        if keep {
            //@ close Node(*n, next, value);
            //@ close lseg(*n, std::ptr::null_mut());
            filter_nodes(&raw mut (**n).next, p);
            //@ open lseg(next, std::ptr::null_mut());
            //@ close lseg(*n, std::ptr::null_mut());
        } else {
            let next_ = (**n).next;
            //@ open Node(*n, next_, value);
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ close lseg(*n, std::ptr::null_mut());
            filter_nodes(n, p);
            //@ close lseg(*n, std::ptr::null_mut());
        }
    } else {
        //@ close lseg(*n, std::ptr::null_mut());
    }
}

//@ req lseg(n, std::ptr::null_mut());
//@ ens true;
unsafe fn dispose_nodes(n: *mut Node)
{
    //@ open lseg(n, std::ptr::null_mut());
    if !n.is_null() {
        //@ open Node(n, ?next, ?value);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    } else {
        //@ close lseg(n, std::ptr::null_mut());
    }
}

impl Stack {
    //@ req true;
    //@ ens Stack(result);
    unsafe fn create() -> *mut Stack
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
    
    //@ req Stack(stack) &*& Node(?n, (*stack).head, value);
    //@ ens Stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open Stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Node(n, (*stack).head, value);
        //@ open lseg((*stack).head, std::ptr::null_mut());
        //@ close lseg(n, std::ptr::null_mut());
        (*stack).head = n;
        //@ close Stack(stack);
    }

    //@ req Stack(stack) &*& (*stack).head != std::ptr::null_mut();
    //@ ens Stack(stack);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open Stack(stack);
        let head = (*stack).head;
        //@ open lseg(head, std::ptr::null_mut());
        //@ open Node(head, ?next, ?value);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack);
        result
    }
    
    //@ req Stack(stack);
    //@ ens Stack(stack);
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    {
        //@ open Stack(stack);
        filter_nodes(&raw mut (*stack).head, p);
        //@ close Stack(stack);
    }
    
    //@ req Stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open Stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

//@ req true;
//@ ens result == (x != 20);
unsafe fn neq_20(x: i32) -> bool
{
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        //@ close Node(?n1, std::ptr::null_mut(), 10);
        Stack::push(s, 10);
        //@ close Node(?n2, n1, 20);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}