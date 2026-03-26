use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Nodes(n: *mut Node;) =
    if n == 0 {
        true
    } else {
        alloc_block(n as *mut u8, Layout::new_::<Node>()) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?value &*&
        struct_Node_padding(n) &*&
        Nodes(next)
    };

pred Stack(s: *mut Stack;) =
    alloc_block(s as *mut u8, Layout::new_::<Stack>()) &*&
    (*s).head |-> ?head &*&
    struct_Stack_padding(s) &*&
    Nodes(head);

pred_ctor I32Pred(p: I32Predicate)(value: i32) = p(value) == true || p(value) == false;
@*/

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req *n |-> ?node &*& Nodes(node) &*& is_I32Predicate(p);
//@ ens *n |-> ?node2 &*& Nodes(node2) &*& is_I32Predicate(p);
{
    if !(*n).is_null() {
        //@ open Nodes(node);
        let keep = p((**n).value);
        if keep {
            filter_nodes(&raw mut (**n).next, p);
            //@ close Nodes(*n);
        } else {
            let next_ = (**n).next;
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    } else {
        //@ open Nodes(node);
        //@ close Nodes(node);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req Nodes(n);
//@ ens true;
{
    //@ open Nodes(n);
    if !n.is_null() {
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
        //@ close Nodes(0 as *mut Node);
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
        (*stack).head = n;
        //@ close Nodes(n);
        //@ close Stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack(stack) &*& (*stack).head |-> ?head &*& head != 0 as *mut Node;
    //@ ens Stack(stack);
    {
        //@ open Stack(stack);
        let head = (*stack).head;
        //@ open Nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack);
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req Stack(stack) &*& is_I32Predicate(p);
    //@ ens Stack(stack) &*& is_I32Predicate(p);
    {
        //@ open Stack(stack);
        filter_nodes(&raw mut (*stack).head, p);
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

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        //@ assert is_I32Predicate(neq_20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}