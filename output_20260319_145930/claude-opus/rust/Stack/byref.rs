use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Nodes(n: *mut Node; count: i32) =
    if n == 0 {
        count == 0
    } else {
        alloc_block_Node(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?value &*&
        Nodes(next, ?rest) &*&
        count == rest + 1
    };

pred Stack(s: *mut Stack;) =
    alloc_block_Stack(s) &*&
    (*s).head |-> ?head &*&
    Nodes(head, _);
@*/

type I32Predicate = unsafe fn(i32) -> bool;

/*@
pred is_i32_predicate(p: I32Predicate) = true;
@*/

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req *n |-> ?node &*& Nodes(node, _) &*& is_i32_predicate(p);
//@ ens *n |-> ?new_node &*& Nodes(new_node, _) &*& is_i32_predicate(p);
{
    //@ open Nodes(node, _);
    if !(*n).is_null() {
        let keep = p((**n).value);
        if keep {
            filter_nodes(&raw mut (**n).next, p);
            //@ close Nodes(*n, _);
        } else {
            let next_ = (**n).next;
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    } else {
        //@ close Nodes(*n, _);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req Nodes(n, _);
//@ ens true;
{
    //@ open Nodes(n, _);
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
        //@ close Nodes(0 as *mut Node, 0);
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
        //@ close Nodes(n, _);
        //@ close Stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack(stack) &*& (*stack).head |-> ?head &*& head != 0;
    //@ ens Stack(stack);
    {
        //@ open Stack(stack);
        let head = (*stack).head;
        //@ open Nodes(head, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack);
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req Stack(stack) &*& is_i32_predicate(p);
    //@ ens Stack(stack) &*& is_i32_predicate(p);
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
//@ ens true;
{
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        //@ close is_i32_predicate(neq_20);
        Stack::filter(s, neq_20);
        //@ open is_i32_predicate(neq_20);
        Stack::dispose(s);
    }
}