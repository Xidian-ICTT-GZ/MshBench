use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

/*@
pred Nodes(n: *mut Node; count: i32) =
    if n == 0 {
        count == 0
    } else {
        (*n).next |-> ?next &*&
        (*n).value |-> ?value &*&
        alloc_block(n, std::alloc::Layout::new_::<Node>()) &*&
        Nodes(next, ?rest_count) &*&
        count == rest_count + 1
    };

pred Stack(s: *mut Stack;) =
    (*s).head |-> ?head &*&
    alloc_block(s, std::alloc::Layout::new_::<Stack>()) &*&
    Nodes(head, _);
@*/

/*@
lem Nodes_split(n: *mut Node)
    req Nodes(n, ?count) &*& n != 0;
    ens (*n).next |-> ?next &*&
        (*n).value |-> ?value &*&
        alloc_block(n, std::alloc::Layout::new_::<Node>()) &*&
        Nodes(next, ?rest_count) &*&
        count == rest_count + 1;
{
    open Nodes(n, count);
}
@*/

/*@
lem Nodes_join(n: *mut Node)
    req (*n).next |-> ?next &*&
        (*n).value |-> ?value &*&
        alloc_block(n, std::alloc::Layout::new_::<Node>()) &*&
        Nodes(next, ?rest_count);
    ens Nodes(n, rest_count + 1);
{
    close Nodes(n, rest_count + 1);
}
@*/

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
//@ req Nodes(n, ?count);
//@ ens Nodes(result, ?new_count);
{
    //@ open Nodes(n, count);
    if n.is_null() {
        //@ close Nodes(std::ptr::null_mut(), 0);
        std::ptr::null_mut()
    } else {
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);

            (*n).next = next;

            //@ close Nodes(n, ?new_count);
            n
        } else {
            next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req Nodes(n, ?count);
//@ ens true;
{
    //@ open Nodes(n, count);
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

        //@ close Nodes(std::ptr::null_mut(), 0);
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
        //@ close Nodes(n, ?new_count);
        (*stack).head = n;
        //@ close Stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack(stack) &*& (*stack).head |-> ?head &*& head != 0 &*& Nodes(head, ?count) &*& count > 0;
    //@ ens Stack(stack);
    {
        //@ open Stack(stack);
        let head = (*stack).head;
        //@ open Nodes(head, count);

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
//@ ens true;
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