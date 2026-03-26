use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Node(node: *mut Node; next: *mut Node, value: i32) =
    alloc_block(node, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(node) &*&
    (*node).next |-> next &*&
    (*node).value |-> value;
@*/

/*@
pred nodes(n: *mut Node) =
    n.is_null() ?
        true
    :
        Node(n, next, _) &*& nodes(next);
@*/

/*@
pred Stack(stack: *mut Stack) =
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> head &*&
    nodes(head);
@*/

type I32Predicate = unsafe fn(i32) -> bool;

//@ req nodes(*n);
//@ ens nodes(*n);
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
{
    //@ open nodes(*n);
    if !(*n).is_null() {
        //@ open Node(*n, next, value);
        let keep = p((**n).value);
        if keep {
            //@ close Node(*n, next, value);
            //@ close nodes(*n);
            filter_nodes(&raw mut (**n).next, p);
            //@ open nodes((**n).next);
            //@ open Node(*n, next, value);
            //@ close Node(*n, next, value);
            //@ close nodes(*n);
        } else {
            let next_ = (**n).next;
            //@ close Node(*n, next, value);
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
            //@ close nodes(*n);
        }
    } else {
        //@ close nodes(*n);
    }
}

//@ req nodes(n);
//@ ens true;
unsafe fn dispose_nodes(n: *mut Node)
{
    //@ open nodes(n);
    if !n.is_null() {
        //@ open Node(n, next, value);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
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
        //@ close nodes(std::ptr::null_mut());
        //@ close Stack(stack);
        stack
    }
    
    //@ req Stack(stack) &*& nodes((*stack).head);
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
        //@ close nodes(n);
        (*stack).head = n;
        //@ close Stack(stack);
    }

    //@ req Stack(stack) &*& (*stack).head |-> head &*& head != 0 &*& Node(head, next, value);
    //@ ens Stack(stack) &*& result == value;
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open Stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        //@ open Node(head, next, value);
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
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}