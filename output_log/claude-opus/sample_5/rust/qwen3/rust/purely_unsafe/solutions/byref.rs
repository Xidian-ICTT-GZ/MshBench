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
pred Node_own(n: *mut Node; next: *mut Node, value: i32) =
    alloc_block(n as *mut u8, Layout::new_::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;

pred Nodes(n: *mut Node; values: list<i32>) =
    if n == std::ptr::null_mut() {
        values == nil
    } else {
        Node_own(n, ?next, ?v) &*&
        Nodes(next, ?rest) &*&
        values == cons(v, rest)
    };

pred Stack_own(s: *mut Stack; head: *mut Node) =
    alloc_block(s as *mut u8, Layout::new_::<Stack>()) &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> head;

pred Stack_pred(s: *mut Stack; values: list<i32>) =
    Stack_own(s, ?head) &*&
    Nodes(head, values);
@*/

/*@
lem Nodes_null_inv()
    req Nodes(std::ptr::null_mut(), ?vs);
    ens Nodes(std::ptr::null_mut(), vs) &*& vs == nil;
{
    open Nodes(std::ptr::null_mut(), vs);
    close Nodes(std::ptr::null_mut(), vs);
}
@*/

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req (*n) |-> ?head &*& Nodes(head, ?xs);
//@ ens (*n) |-> ?new_head &*& Nodes(new_head, ?ys) &*& length(ys) <= length(xs);
{
    //@ open Nodes(head, xs);
    if !(*n).is_null() {
        let keep = p((**n).value);
        if keep {
            //@ close Nodes(*n, xs);
            //@ open Nodes(*n, xs);
            //@ let old_n = *n;
            //@ open Node_own(old_n, ?next_node, ?val);
            filter_nodes(&raw mut (**n).next, p);
            //@ close Node_own(old_n, (**n).next, val);
            //@ close Nodes(old_n, _);
        } else {
            let next_ = (**n).next;
            //@ open Node_own(*n, next_, _);
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    } else {
        //@ close Nodes(std::ptr::null_mut(), nil);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req Nodes(n, ?xs);
//@ ens true;
{
    //@ open Nodes(n, xs);
    if !n.is_null() {
        //@ open Node_own(n, ?next, ?v);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack_pred(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close_struct(stack);
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(std::ptr::null_mut(), nil);
        //@ close Stack_own(stack, std::ptr::null_mut());
        //@ close Stack_pred(stack, nil);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack_pred(stack, ?xs);
    //@ ens Stack_pred(stack, cons(value, xs));
    {
        //@ open Stack_pred(stack, xs);
        //@ open Stack_own(stack, ?old_head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close_struct(n);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Node_own(n, old_head, value);
        //@ close Nodes(n, cons(value, xs));
        //@ close Stack_own(stack, n);
        //@ close Stack_pred(stack, cons(value, xs));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack_pred(stack, ?xs) &*& xs != nil;
    //@ ens Stack_pred(stack, tail(xs)) &*& result == head(xs);
    {
        //@ open Stack_pred(stack, xs);
        //@ open Stack_own(stack, ?old_head);
        let head = (*stack).head;
        //@ open Nodes(head, xs);
        //@ open Node_own(head, ?next_node, ?val);

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        //@ close Stack_own(stack, next_node);
        //@ close Stack_pred(stack, tail(xs));
        result
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req Stack_pred(stack, ?xs);
    //@ ens Stack_pred(stack, ?ys) &*& length(ys) <= length(xs);
    {
        //@ open Stack_pred(stack, xs);
        //@ open Stack_own(stack, ?old_head);
        filter_nodes(&raw mut (*stack).head, p);
        //@ close Stack_own(stack, (*stack).head);
        //@ close Stack_pred(stack, _);
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack_pred(stack, ?xs);
    //@ ens true;
    {
        //@ open Stack_pred(stack, xs);
        //@ open Stack_own(stack, ?head);
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